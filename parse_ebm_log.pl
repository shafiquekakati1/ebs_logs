#!/usr/bin/env perl

#
# File		: parse_ebm_log.pl
# Purpose	: Parse EBM logs for troubleshooting purposes.
# updated by	: EWENHAN + EENZCHA
# Date		: 2011-01-20
#

### ==========================================================================
###     REVISION LOG
### ==========================================================================
### Date    Name     What
### ------- -------- ---------------------------------------------------------
### 210630  eziajxi  PCTR-32203 - Wrong ouput when parse AMF event with -l option


require 5.6.1;
use Getopt::Std;
use strict;
use POSIX;
use File::Basename;
use Cwd;
use Symbol;
use Time::Local;
use Digest::MD5;

my $file = "./ebm.xml";
my $cause_xml = "./ebm_cause_codes.xml";
my ($FFV_XML,$FIV_XML)=("","");
my %use_param;

my $n = 8;

my $OUT = Symbol::gensym();;
$OUT =  \*STDOUT;
local *FH;
my($CP,$TAIL)=("cp","tail");
my $prog=basename $0;
my $ebs_log_binary_DIR = "/tmp/OMS_LOGS/ebs/ready";
my $ebs_log_binary;
my $ebs_file_inarg;
my $total_content;
my $midnight_time_threshold = 12;
##Current EBM record
my $this_record_content_BIT;
my $this_record_content_BIT_index;
my $this_record_length;
my $this_record_length_actual;
my $this_record_content;
my $event_record;
my %event_record;

##Arguments
my %opts;
my $rat_opts;
my $event_type_opts;
my $mode = "detail";
my $param_mode = "all";
my $use_hash_len = 32;
my $usechild = 0;
my ($l_attach_times,$l_attach_duration,$l_attach_first_time,$l_attach_last_time) = (0,0,"","");
my ($l_attach_total_times,$l_attach_total_duration,$l_attach_first_time1) = (0,0,"");
my ($from_time,$to_time) = ("","");
my %l_serv_req;
my %l_serv_req_total;


##Header
my ($FFV,$FIV,$year,$month,$day,$hour,$minute,$second);

##Format
my $delimiter = "\n";
my $pr_all=0;

##Counters
my $nbr_unknown_event = 0;
my $total_nbr_events = 0;
my $nbr_hit = 40;

##Filters
my @filters;
my %filters;
my $unsuccessful = "false";
my $unsuccessful_pattern = "";
my $rat = "false";
my $rat_pattern = "";
my $imsi = "false";
my $imsi_pattern = "";
my $imeisv ="false";
my $imeisv_pattern = "";
my $cause_code = "false";
my $cause_code_pattern = "";
my $apn = "false";
my $apn_pattern = "";
my $sub_cause_code = "false";
my $sub_cause_code_pattern = "";
my $decode_all = "true";
my $filter_hit = 1;
my $parameter = "";
my $parameter_value = "";

## hash tables for xml parse
## event_id => attend_flag
my %event_list_tab = ();
## event_name => counter_value
my %event_counter_tab = ();
## cause code
my %cause_code = ();
my $ie_types = {};
my $tmp_types = {};
my $enums = {};
my $all_events = {};
my $all_ies = {};
my $event_str = "";

## summary mode
my %counters;
my %cc_stats;
my %sub_cc_stats;

## decode function for each IE type
my %decode_types = (
			'uint' => \&decode_uint,
			'enum' => \&decode_enum,
			'bytearray' => \&decode_bytearray,
			'ipaddress' => \&decode_ipaddress,
			'ipaddressv4' => \&decode_ipaddressv4,
			'ipaddressv6' => \&decode_ipaddressv6,
			'dnsname' => \&decode_dnsname,
			'tbcd' => \&decode_tbcd,
			'ibcd' => \&decode_ibcd);

## md5 generator
my $md5_ctx     = Digest::MD5->new;
my $md5_salt    = "E_Salt";
my $md5_encrypt = "false";

#	element type (hash, parameter and structure): ie_info
#	{	name,		// string, type name
#		elName,		// IE name
#		isLeaf,		// 1-true, 0-false
#		type,		// get from xml, atom or structure
#		len,			// atom type length
#		level,		// structure level
#		useValid,		// true|false
#		optional,		// true|false
#		seqLen,		// seqmaxlen
#		childNum,	// length of child array
#	}

#   all_events{event_it}{ies} :[ie_info,,,,]		// array of ie_info


my ($wId, $sec);
my @working= qw(- \ | /);

#####################################################
sub print_caution {
	my $sep = "\t" . '!' x 60 . "\n\n";
	print $OUT $sep;
	print $OUT "\tCAUTION!\tCAUTION!\tCAUTION!\tCATION!\n\n";
	print $OUT "\t$prog is not intended to be ran on the SGSN-MME node, it might impact the capacity of the\n";
	print $OUT "\tSGSN-MME. Running this command may cause heavy CPU load, depending on the size of the input\n";
	print $OUT "\t file. Please install the script on another UNIX machine, where EBM logs are collected.\n";
	print $OUT $sep;
}

#####################################################
sub usage {
	my $sep = "\t" . '-' x 50 . "\n\n";
	my $pr = 'user@host > ';
	print_caution;
	print $OUT "USAGE: \n";
	print $OUT "\t$prog {-h| -s [-d directory] [-f logfile] [-o outfile] [-p delimiter] [-u] [-r gsm|wcdma]\n";
	print $OUT "\t\t[-e event[,event,...]] [-c cause_code[,cause_code,...]] [-z sub_cause_code[,sub_cause_code,...]]\n";
	print $OUT "\t\t[-i imsi[,imsi,...] ] [-t tac[,tac,...]] [-a apn[,apn,...]] [-n ie_name[,ie_name,...]]\n";
	print $OUT "\t\t[-v ie_value[,ie_value...]] [-l] [-x xml_directory] [-A] [-S] [-D from_time [to_time]]\n";
	print $OUT "\t\t[-C cause_code|sub_cause_code] [-L]\n";
	print $OUT "\n\tThis program can be used to parse EBM logs. The files ebm.xml and ebm_cause_codes.xml should be ";
	print $OUT "\n\tput under the same dircetory with this parser script if it's not running on the node.\n";

	print $OUT "\nOPTIONS:";
	print $OUT "\n\t-h: Help.\n";
	print $OUT "\n\t-s: Summary mode, prints summary statistics for the processed files.\n";
	print $OUT "\n\t-p: Print event records in delimiter separated columns.\n";
	print $OUT "\n\t-u: Filter on unsuccessful events.\n";
	print $OUT "\n\t-r: Filter on rat type.\n";
	print $OUT "\n\t-e: Filter on event type. * can be used to match any character, the last asterisk can be obmitted.\n";
	print $OUT "\n\t-c: Filter on cause codes.\n";
	print $OUT "\n\t-z: Filter on sub cause codes.\n";
	print $OUT "\n\t-i: Filter on imsi numbers.\n";
	print $OUT "\n\t-t: Filter on TACs. TAC=Type Approval Code, first eight digits in IMEI.\n";
	print $OUT "\n\t-a: Filter on APNs.\n";
	print $OUT "\n\t-n: Filter on specific IE name, like ue_restoration.\n";
	print $OUT "\n\t-v: Filter on specific IE value, like true.\n";
	print $OUT "\n\t-l: Print as table. If missing option -p,then the default delimiter will be used\n";
    print $OUT "\n\t-y: Specify a salt value (random value) used for anonymization of sensitive information.\n";
	print $OUT "\n\t-f: Specify logfile (with absolute path) to parse, otherwise $prog tries to parse :\n";
	print $OUT "\t    all ebm log files in current working directory - if $prog runs outside SGSN-MME node or \n";
	print $OUT "\t    all logs located in the $ebs_log_binary_DIR - if the script runs on the SGSN-MME node.\n";
	print $OUT "\n\t-d: Specify log directory - overwrite the default log directory value.\n";
	print $OUT "\n\t-o: Redirect output into file outfile. Please note that it is not possible to use  \n";
	print $OUT "\t    UNIX command \">\" for redirecting of output on the SGSN-MME node. Use -o instead.\n";
	print $OUT "\n\t-x: Specify the directory of ebm.xml and ebm_cause_codes.xml, overwrite the default value.\n";
	print $OUT "\n\t-D: Specify the duration, time format 'HH:MM:SS'. If without 'to_time', then till the end of file.\n";
	print $OUT "\n\t-A: Display the accumulated attach duration of all successful L_Attach events in seconds in a\n";
	print $OUT "\t    specified log file or directory.\n";
	print $OUT "\n\t-C: Display the meaning of the specified cause code.\n";
	print $OUT "\n\t-L: Display the meaning of all the cause code, sub cause code and bearer code.\n";
	print $OUT "\n\t-S: Display the paging information for each TA in specified log file or directory.\n";
    print $OUT "\n\t-Y: Enable anonymization of sensitive information, such as imsi, msidsn,tac and so on. The output could be used to analyze movement pattern for probability paging. Suggest that customer use -y to specify the salt value for anonymization. If -y is not used, a default value will be used for anonymization.\n";
	print $OUT "\t    The paging information is calculated from the L_Service_Request event.\n";
	print $OUT "\n\t-T: print the timestamp 'time = YYYY-MM-DD HH:MM:SS:FFF' instead of the time_hour, time_minute,\n";
	print $OUT "\t    time_second and time_millisecond.\n";
    print $OUT "\n\t-H: If anonymization of sensitive information is used, this parameter specifies the truncated number of the hash value,\n";
    print $OUT "\t    Ericsson recommends the truncated number is configured in the range from 8 to 32.\n";
    print $OUT "\n\t-F: Filter the EBM parameters defined in the /tmp/DPE_SC/LoadUnits/ttx/bin/params.txt file.\n";

	print $OUT "\nNOTE:\n";

	print $OUT "\tOnly the options -f, -d or -o are allowed to be used together with the options -A or -S. Any other\n";
	print $OUT "\toptions that are used together with the options -A or -S are omitted.The options -A and -S can be used\n";
	print $OUT "\ttogether or separately.\n";
        print $OUT "\tOptions -n and -v must be used together, if want to filter on multi parameter names (match all of them),\n";
        print $OUT "\t-n and -v options should be used as lists, names and values are in the same order and separated with ','.\n";
        print $OUT "\tIf specify muti value for other options (like -i imsi1,imsi2), the script will match each of them.\n";

	print $OUT "\nEXAMPLES:\n";
	print $OUT $sep;
	print $OUT "\tFilter on unsuccessful events\n";
	print $OUT "\t$pr$prog -u -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on attach event and all events named with act\n";
	print $OUT "\t$pr$prog -e 'att,*act' -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on L_DEDICATED_BEARER_ACTIVATE event\n";
	print $OUT "\t$pr$prog -e 'l_d*_a' -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on attach, activation and rau events for GSM\n";
	print $OUT "\t$pr$prog -r gsm -e 'att,act,rau'  -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on cause code #9 for israu for WCDMA\n";
	print $OUT "\t$pr$prog -r wcdma -e israu -c 9 -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on the IMSI numbers 240999800416785 240999802602314\n";
	print $OUT "\t$pr$prog -i 240999800416785,240999802602314 -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on the tac 123456\n";
	print $OUT "\t$pr$prog -t 12345678 -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on activations on the apn apn2sgsn350-2.ericsson.com.mnc021.mcc123.gprs\n";
	print $OUT "\t$pr$prog -e act -a apn2sgsn350-2.ericsson.com.mnc021.mcc123.gprs -d ./\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on duration, from '10:20:30' to '10:30:20'.\n";
	print $OUT "\t$pr$prog -S -d ./ebs_logs/ -D \"10:20:30 10:30:20\"\n\n";
	print $OUT $sep;
	print $OUT "\tFilter on event 'l_tau', in which the value of IE 'ue_restoration' is true and 'tau_type' is 'isc_tau'\n";
	print $OUT "\t$pr$prog -e l_tau -n ue_restoration,tau_type -v true,isc_tau\n\n";
	print $OUT $sep;
	print $OUT "\tPrint values in table format. Use delimiter '|'\n";
	print $OUT "\t$pr$prog -l -p '|' \n\n";
	print $OUT $sep;
        print $OUT "\tPrint values in table format with timestamp 'time = YYYY-MM-DD HH:MM:SS:FFF'. Use delimiter '|'\n";
        print $OUT "\t$pr$prog -l -T -p '|' \n\n";
        print $OUT $sep;
	print $OUT "\tEBM summary for all logs located in the current directory. Note: Script runs on another UNIX machine\n";
	print $OUT "\t$pr$prog -s \n\n";
	print $OUT $sep;
	print $OUT "\tEBM summary for all logs located in the directory /tmp/ebs_logs.\n";
	print $OUT "\t$pr$prog -s -d /tmp/ebs_logs\n\n";
	print $OUT $sep;
	print $OUT "\tPrint the successful L_ATTACH event duration in a specified log file.\n";
	print $OUT "\t$pr$prog -A -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
	print $OUT $sep;
	print $OUT "\tPrint the paging information in the specified log directory.\n";
	print $OUT "\t$pr$prog -S -d ./ebs_logs/\n\n";
	print $OUT $sep;
	print $OUT "\tPrint the log with UE's sensitive information being anonymous with default salt value.\n";
    print $OUT "\t$pr$prog -Y -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
    print $OUT $sep;
    print $OUT "\tPrint the log with UE's sensitive information being anonymous by a given salt value abs.\n";
    print $OUT "\t$pr$prog -Y -y abs -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
    print $OUT $sep;
    print $OUT "\tTruncate the number of has value, and filter the EBM parameters.\n";
    print $OUT "\t$pr$prog -F -Y -y abs -H 8 -f /tmp/A20081119.0541+0100-20081119.0542+0100_1_ebs.28\n\n";
    print $OUT $sep;
	print $OUT "\tPrint this help message\n";
	print $OUT "\t$pr$prog -h \n\n";
	print $OUT $sep;
	exit 0;
}

#####################################################
sub logg {
	my ($msg_type,$msg_txt)=@_;
	my ($sec,$min,$hour,$day,$mon,$year)=localtime;
	my $date=sprintf("%d-%02d-%02d %02d:%02d:%02d",$year+1900,$mon+1,$day,$hour,$min,$sec);

	if($msg_type =~ /^info/) {
	        print $OUT  ( "$date\tINFO:\t$msg_txt\n");
	}elsif ($msg_type =~ /^warn/) {
	       print $OUT  ("$date\tWARNING:\t$msg_txt\n");
	}elsif ($msg_type =~ /^error/) {
	        print $OUT ( "$date\tERROR:\t$msg_txt\n");
		exit 1;
	}elsif ($msg_type =~ /^output/) {
	        print $OUT  ( "$date\tINFO:\t$msg_txt\n");
	}elsif ($msg_type =~ /^nolog_error/) {
	        print("\tERROR:\t$msg_txt\n");
		exit 1;
	}elsif ($msg_type =~ /^no_format/) {
	        print("$msg_txt");
	}
}

#####################################################
sub modify_opt {
	my ($pattern)=@_;
	my $ret="";
	my @arr=split(/\s*\,\s*|\s+/,$pattern);
	foreach my $e (@arr) {
		$ret .= "^$e". '$|';
	}
	$ret =~ s/(.*)\|$/$1/;
	return $ret;
}

#####################################################
# It's used to rebuild the regular expression (change * to .*).
#####################################################
sub build_event_list {
	my ($event) = @_;
	my $matched = 0;
	$event =~  s/\*/\.\*/g;

	foreach my $key (keys %{$all_events}){
		if ( $all_events->{$key}{name} =~ /^$event/i){
			$event_list_tab{$key} = 1;
			$matched = 1;
		}
	}

	if ($matched == 0){
		print("\nERROR: Event type option \"$event\" can't match any event defined in ebm.xml. Defined events:\n");
		foreach my $key (keys %{$all_events}){
			print "\t$all_events->{$key}{name}\n";
		}
		print(" \nNote: * can be used as wildcard, last asterisk can be obmitted. Not case-sensitive.\n");
		print("Example: \"$prog -e l_d*_a\" to filter event \"L_DEDICATED_BEARER_ACTIVATE\".\n\n");
		exit 0;
	}
}

#####################################################
# It's used to rebuild the regular expression (change * to .*).
#####################################################
sub get_opts {
	if (exists $opts{'A'} && exists $opts{'S'}) {
		$opts{'e'}="l_attach,l_service_request";
		$mode = "counter";
	}elsif (exists $opts{'A'}) {
		$opts{'e'}="l_attach";
		$mode = "counter";
	}elsif (exists $opts{'S'}) {
		$opts{'e'}="l_service_request";
		$mode = "counter";
	}elsif (exists $opts{s}) {
		$mode = "summary";
	} else{

		if (exists $opts{'l'}) {
			$pr_all= 1;
			$delimiter=';';
		}
		if (exists $opts{'Y'}) {
                        $md5_encrypt="true";
                        if(exists($opts{'y'})){
                               $md5_salt=$opts{'y'};
                        }
                }
		if (exists $opts{'p'}) {
			if(length($opts{'p'})>0){
				$delimiter=$opts{'p'};
			}else{
				$delimiter=';';
			}
		}
		if (exists $opts{'u'}) {
			$unsuccessful="true";
		}
		if (exists $opts{'r'}  && $opts{'r'} =~ /\w/) {
			$rat = "true";
			$rat_pattern = modify_opt($opts{'r'});
                        if (! ("gsm" =~ /$rat_pattern/ || "wcdma" =~ /$rat_pattern/ || "lte" =~ /$rat_pattern/)) {
                                print("ERROR: Radio access type option can be gsm|wcdma|lte. Exiting...\n");
				exit 0;
			}
		}
		if (exists $opts{'e'}) {
			$decode_all = "false";
		}
		if (exists $opts{'c'} && $opts{'c'} =~ /\d/) {
			$cause_code = "true";
			$cause_code_pattern = modify_opt($opts{'c'});
		}
		if (exists $opts{'z'} && $opts{'z'} =~ /\d/) {
			$sub_cause_code = "true";
			$sub_cause_code_pattern = modify_opt($opts{'z'});
		}
		if (exists $opts{'i'}  && $opts{'i'} =~ /\d/) {
			$imsi = "true";
			$imsi_pattern = modify_opt($opts{'i'});
		}
		if (exists $opts{'t'} && $opts{'t'} =~ /\d/) {
			$imeisv = "true";
			$imeisv_pattern  = modify_opt($opts{'t'});
		}
		if (exists $opts{'a'}  && $opts{'a'} =~ /\w/) {
			$apn = "true";
			$apn_pattern = modify_opt($opts{'a'});
		}
		if (exists $opts{'n'}  && $opts{'n'} =~ /\w/) {
			if (! exists $opts{'v'}){
				print "ERROR: -n should be used together with -v! Exit ...\n";
				exit 1;
			}
			$parameter = $opts{'n'};
		}
		if (exists $opts{'v'}  && $opts{'v'} =~ /\w/) {
			if (! exists $opts{'n'}){
				print "ERROR: -v should be used together with -n! Exit ...\n";
				exit 1;
			}
			$parameter_value = $opts{'v'};
		}
		if (exists $opts{'D'}  && $opts{'D'} =~ /\d/) {
			($from_time,$to_time)=split(/\s+/,$opts{'D'});
			my @time = (0,0,0); #hour:minute:second
			@time = split(/\.|\:/,$from_time);
			$from_time = sprintf("%02d:%02d:%02d",@time);
			if ($to_time !~ /\d/){
				$to_time = "25:00:00";
			}else{
				@time = split(/\.|\:/,$to_time);
				$to_time = sprintf("%02d:%02d:%02d",@time);
			}
		}
	}
	if (exists $opts{'x'}) {
		$file = $opts{'x'} . "/ebm.xml";
		$cause_xml =$opts{'x'}.  "/ebm_cause_codes.xml";
	}
    if (exists $opts{'F'}) {
        $param_mode="select";
    }
    if (exists $opts{'H'}) {
        $use_hash_len=$opts{'H'};
    }
	if (exists $opts{'f'}) {
		$ebs_file_inarg = $opts{'f'};
	}
	&set_default_dir;
}

#####################################################
# Redirect the result into a file.
#####################################################
sub redirect {
	if ($opts{o}=~/\w+/) {
		if (! (open(FH,"> $opts{o}"))) {
			die ( "Failed to open log file $opts{o} - $!");
		}
		print $OUT "The output will be redirected into file: " .  $opts{o} . "\n";
		print $OUT "Please be patient! Parsing can take a while, depending on the size of input files!\n";
		$OUT=\*FH;
		print $OUT "# Created by $prog\n";
	} else {
		$OUT=\*STDOUT;
	}
}

#####################################################
sub arraydir{
	my $dir = shift;
	opendir my $dh, $dir or logg ('warn',"can't opendir $dir - $!");;
	my @arr = ();
	while( my $file = readdir($dh) ) {
		next if $file =~ m[^\.{1,2}$];
		my $path = $dir .'/' . $file;
		push(@arr, $file) if -d $path;
	}
	return @arr;
}

#####################################################
sub set_default_dir {
	if (exists $opts{'d'}) {
		$ebs_log_binary_DIR = $opts{'d'};
	}else{
		my $snode=&get_sgsn_node;
		if($snode){
			$ebs_log_binary_DIR="/tmp/OMS_LOGS/ebs/ready";
		}else{
			$ebs_log_binary_DIR=cwd() ;
		}
	}
}

#####################################################
# Parse Cause Code and Sub Cause Code defined in ebm_cause_codes.xml.
#####################################################
sub parse_cause
{
	my ($protocol_name, $cause_name, $cc, $description, $action, $type,$line) = ("","",0,"","","","");

	if ( -r $cause_xml ){
		open(IN, "< $cause_xml") or logg('error',"Failed to open ebm_cause_codes.xml: $cause_xml - $!");
	}elsif ( -r "/tmp/DPE_SC/ApplicationData/GSN/ebm_cause_codes.xml" && !exists $opts{'x'}) {
		$cause_xml = "/tmp/DPE_SC/ApplicationData/GSN/ebm_cause_codes.xml";
		open(IN, "< $cause_xml") or logg('error',"Failed to open '/tmp/DPE_SC/ApplicationData/GSN/ebm_cause_codes.xml' - $!");
	}else{
		my $msg = "Failed to open ebm_cause_codes.xml in current directory," . $opts{'x'} ." and node directory. -$!\n";
		$msg .= ' ' x 24 . "Please specify the XML file direcroty with option '-x' \n";
		$msg .= ' ' x 24 . "Or get to current directory from '/tmp/DPE_SC/ApplicationData/GSN/\n";
		logg('error',$msg);
	}

	while (<IN>) {
                if ( $_ !~ /^\s*\</) {
                        $line .= $_;
                }else {
                        $line = $_;
                }
		if ( $line =~ /\<protocol name="(.*?)"\>/) {
			$protocol_name = lc($1);
		}elsif ( $line =~ /\<bearercausecodes\>/) {
			$protocol_name = "bearer";
		}elsif ( $line =~ /\<subcausecodes\>/) {
			$protocol_name = "sub";
		}elsif ( $line =~ /\<(.*?) value="(\d+)"\>/) {
			$type = $1;
			$cc = $2;
		}elsif ( $line =~ /\<name\>(.*)\<\/name\>/s) {
			$cause_name = lc($1);
			$cause_name =~ s/_/ /g;
		}elsif ( $line =~ /\<description\>(.*)\<\/description\>/s) {
			$description = $1;
		}elsif ( $line =~ /\<action\>(.*)\<\/action\>/s) {
			$action = $1;
			$cause_code{$protocol_name}{$cc}{'name'} = "#".$cc."(".$cause_name.")";
			$cause_code{$protocol_name}{$cc}{'description'} = "$description";
			$cause_code{$protocol_name}{$cc}{'action'} = "$action";
			$cause_code{$protocol_name}{$cc}{'type'} = "$type";
		}

	}
	close(IN);
}

sub print_cause_code{
	if (exists $opts{L}) {
		foreach my $protocol_name (keys %cause_code) {
			print "\n\n######## $protocol_name Cause Codes ######## \n";
			print "-" x 50 ."\n";
			foreach my $cc (sort { $a <=> $b } (keys %{$cause_code{$protocol_name}})) {
				print "$cause_code{$protocol_name}{$cc}{'type'}". "$cause_code{$protocol_name}{$cc}{'name'}\n";
				print "  Description: $cause_code{$protocol_name}{$cc}{'description'}\n";
				print "  Action: $cause_code{$protocol_name}{$cc}{'action'}\n\n";
			}
		}
	}elsif (exists $opts{C}) {
		my $cc = $opts{C};
		foreach my $protocol_name (keys %cause_code) {
			if (exists  $cause_code{$protocol_name}{$cc}{'name'}) {
				print "\n\n######## $protocol_name Cause Codes ######## \n";
				print "$cause_code{$protocol_name}{$cc}{'type'}". "$cause_code{$protocol_name}{$cc}{'name'}\n";
				print "  Description: $cause_code{$protocol_name}{$cc}{'description'}\n";
				print "  Action: $cause_code{$protocol_name}{$cc}{'action'}\n\n";
			}
		}
	}
}
sub print_events
{
	foreach my $event_id (sort (keys %{$all_events}))
	{
		print "\n\n";
		print "$event_id -- $all_events->{$event_id}{name}\n";
		#foreach my $elem ( @{$all_events->{$event_id}{ies}}) {	#all ies
		for my $i ( 0 .. $#{$all_events->{$event_id}{ies}}) {
			my $elem = $all_events->{$event_id}{ies}->[$i];
			print "$i:\t" . "   " x ($elem->{level} -1) . "IE_name($elem->{name}),type($elem->{type}),len($elem->{len}),$elem->{level},";
			print "usevalid($elem->{useValid}),optional($elem->{optional}),seqLen($elem->{seqLen}),isLeaf($elem->{isLeaf}),childNum($elem->{childNum})\n";
		}
	}
}

#####################################################
# Parse all IE types (parameter and structure types).
#####################################################
sub parse_all_ie_types
{
	my ($key,$i,$elem);
	foreach $key (keys %{$tmp_types}) {
		push(@{$ie_types->{$key}},
			{
				isLeaf	=>	1,
				type		=>	$tmp_types->{$key}{type},
				len		=>	$tmp_types->{$key}{len},
				name	=>	$key
			}
		);
	}
}

#####################################################
# Parse all IE types and events (parameter and structure types and events).
#####################################################
sub parse_ebm_xml
{
	my ($xmlfile)=@_;
	my ($parseing_el) = 0;
	my ($parseing_ptype) = 0;
	my ($parseing_struct) = 0;
	my ($parseing_event) = 0;
	my $events = {};
	my ($name,$key,$value,$id,$el_name,$isLeaf,$type,$len,$level,$useValid,$optional,$seqLen,$childNum,$childArray)=
		("","","",-1,"",0,"",0,0,undef,undef,undef,0,undef);

	if ( -r $xmlfile ){
		open(IN, "< $xmlfile") or logg('error',"Failed to open ebm.xml: $xmlfile - $!");
	}elsif (-r "/tmp/DPE_SC/ApplicationData/GSN/ebm.xml" && !exists $opts{'x'}) {
		$xmlfile = "/tmp/DPE_SC/ApplicationData/GSN/ebm.xml";
		open(IN, "< $xmlfile") or logg('error',"Failed to open '/tmp/DPE_SC/ApplicationData/GSN/ebm.xml' - $!");
	}else{
		my $msg = "Failed to open ebm.xml in current directory," . $opts{'x'} ." and node directory. -$!\n";
		$msg .= ' ' x 24 . "Please specify the XML file direcroty with option '-x' \n";
		$msg .= ' ' x 24 . "Or get to current directory from '/tmp/DPE_SC/ApplicationData/GSN/'\n";
		logg('error',$msg);
	}

	while (<IN>) {
		if ( /\<parametertypes\>/) {
			$parseing_ptype = 1;
		}elsif ( /\<structuretypes\>/) {
			$parseing_struct = 1;
		}elsif ( /\<events\>/) {
			$parseing_event = 1;
		}elsif ( /\<\/parametertypes\>/) {
			$parseing_ptype = 0;
		}elsif ( /\<\/structuretypes\>/) {
			parse_all_ie_types;
			$parseing_struct = 0;
		}elsif ( /\<\/events\>/) {
			$parseing_event = 0;
		}elsif (/\<ffv\>\s*(.*?)\s*\</i) {
			$FFV_XML = $1;
		}elsif (/\<fiv\>\s*(.*?)\s*\</i) {
			$FIV_XML = $1;
		}

		if ($parseing_ptype == 1){
			if ( /\<name\>\s*(.*?)\s*\<\/name\>/ ) {
				$name = lc($1);
			}elsif ( /\<type\>\s*(.*?)\s*\<\/type\>/ ) {
				$type = lc($1);
			}elsif ( /\<numberofbits\>\s*(.*?)\s*\<\/numberofbits\>/) {
				$len = $1;
			}elsif ( /\<lengthbits\>\s*(.*?)\s*\<\/lengthbits\>/) {
				$len = $1;
			}elsif ( /\<\/parametertype\>/) {
				$tmp_types->{$name}{type} = $type;
                                $tmp_types->{$name}{len} = $len;
			}elsif ( /internal="(.*?)" value="(\d+?)"\>/) {
                        	$value = lc($1);
                        	$key = lc($2);
                                if($value =~ /_cause$/) { $value =~ s/(.*)_cause$/$1/;}
                                elsif($value =~ /_cause2$/) { $value =~ s/(.*)_cause2$/$1_2/;}
				$enums->{$name}->{$key} = $value;
			}
		}

		if ($parseing_struct == 1){
			$name = lc($1) if ( /\<name\>\s*(.*?)\s*\<\/name\>/ );
			$id = $1  if ( /\<id\>\s*(.*?)\s*\<\/id\>/ );
			$el_name = lc($1) if ( /"\>\s*(.*?)\s*\<\// );
			$optional = lc($1) if ( /optional="(.*?)"/ );
			$useValid = lc($1) if ( /usevalid="(.*?)"/ );
			$seqLen = lc($1) if ( /seqmaxlen="(.*?)"/ );
			$type = lc($1) if ( /type="(.*?)"/ );
			if ( /type="(.*?)"/ ) {
				push(@{$ie_types->{$name}},
						{
							name	=>	$el_name,
							isLeaf	=>	0,
							type		=>	$type,
							useValid	=>	$useValid,
							optional	=>	$optional,
							seqLen	=>	$seqLen,
							childArray=>	$childArray
						}
					);

				($el_name,$isLeaf,$type,$len,$level,$useValid,$optional,$seqLen,$childNum,$childArray)= ("",0,"",0,0,undef,undef,undef,0,undef);
			}
		}

		if ($parseing_event == 1){
			$name = uc($1) if ( /\<name\>\s*(.*?)\s*\<\/name\>/ );
			$el_name = lc($1) if ( /"\>\s*(.*?)\s*\<\// );
			$optional = lc($1) if ( /optional="(.*?)"/ );
			$useValid = lc($1) if ( /usevalid="(.*?)"/ );
			$seqLen = lc($1) if ( /seqmaxlen="(.*?)"/ );
			$type = lc($1) if ( /type="(.*?)"/ );
			if ( /\<id\>\s*(.*?)\s*\<\/id\>/ ){
				$id = $1;
				$all_events->{$id}{name} = $name;
			}
			if ( /type="(.*?)"/ ) {
				if (exists $ie_types->{$type} ) {
					push(@{$events->{$id}},
							{
								name	=>	$el_name,
								type		=>	$type,
								type_d	=>	$ie_types->{$type},
								useValid	=>	$useValid,
								optional	=>	$optional,
								seqLen	=>	$seqLen
							}
						);
					if (! $el_name){
						$all_ies->{$type} = "";
					}else{
						$all_ies->{$el_name} = "";
					}

					($el_name,$type,$level,$useValid,$optional,$seqLen)= ("","",0,undef,undef,undef);
				}else{
					print "ERROR\t$type is not defined!\n";
				}
			}
		}
		$all_ies->{"imsi"} = "" if (not exists $all_ies->{"imsi"});
		$all_ies->{"imeisv"} = "" if (not exists $all_ies->{"imeisv"});
	}
	build_event_format($events);

	print_events  if ($opts{'G'} == 1);

	close(IN);
}

sub get_open_expr {
	my $file = shift;
	if($file =~ /gz$/ && -r $file ) {
		return "gzip -cd $file |";
	} else {
		return "< $file";
	}
}

#####################################################
# sort the ebs files to make it in a time order
#####################################################
sub sort_files{
	 my @files = @_;
	 my %sorted = {};
	 my @sort_files=();
	 my $k1;
	 my $k2;

	 foreach (@files) {
	     /A(.*?)_(.*)_/;
	     $sorted{$1}{$2} = $_;
	 }
	 foreach $k1 (sort keys %sorted) {
	     foreach $k2 ( sort {$a <=> $b } keys %{$sorted{$k1}}){
	         push(@sort_files,$sorted{$k1}{$k2});
	     }
	 }
	  return @sort_files;
}

#####################################################
# Parse binary log files.
#####################################################
sub process_ebs_log_files
{
	my @ebs_log_binaries;
	my @ebs_log_binaries1;
	my $start_time;
	my $end_time;
	my @ebs_log_dirs=();
	my @ebs_pdirs=();
	if( defined( $ebs_file_inarg ) ){
		@ebs_log_binaries = ( $ebs_file_inarg );
	}else{
		my $ebs_files=qx(ls -1tr ${ebs_log_binary_DIR}/A*ebs.*[0-9]* 2>/dev/null);
		chomp($ebs_files);
		if($ebs_files =~/\w+/) {
		@ebs_log_binaries=split('\n',$ebs_files);
		@ebs_log_binaries=&sort_files(@ebs_log_binaries);
		}else{
			#We have logs from different nodes.
			@ebs_log_dirs=&arraydir(${ebs_log_binary_DIR});

			foreach my $ebs_dir (@ebs_log_dirs)
			{
				my $ebs_node_files=qx(ls -1 ${ebs_log_binary_DIR}/${ebs_dir}/A*ebs.*[0-9]* 2>/dev/null);
				chomp($ebs_node_files);
				@ebs_log_binaries1=&sort_files(split('\n',$ebs_node_files));
				push(@ebs_log_binaries,@ebs_log_binaries1);
			}
		}
		#@ebs_log_binaries = glob( $ebs_log_binary_DIR . "A*ebs.*" );
	}

        my $c_total = $#ebs_log_binaries +1;
        my $c_curr = 1;
	foreach $ebs_log_binary (@ebs_log_binaries){
               if ($opts{o}=~/\w+/) {
                        print STDERR "\r" . " " x $nbr_hit ."\rNumber of File Processing: ". $c_curr . " / " . $c_total . "   ";
                        $c_curr++;
                        $nbr_hit = 40;
                }

		$total_nbr_events = 0;
		my $new_dir = basename(dirname($ebs_log_binary));
		if(grep(/^$new_dir$/,@ebs_log_dirs)) {
			if(not(grep(/^$new_dir$/,@ebs_pdirs))) {
				print $OUT "###DIRECTORY###\n";
				print $OUT "Current Directory=$new_dir\n\n";
				push(@ebs_pdirs,$new_dir);
			}
		}
		print $OUT "\n###FILE###\n";
		print $OUT "Input file=$ebs_log_binary\n";
		$start_time = localtime();

		open( EBS, get_open_expr($ebs_log_binary) ) or die ( "Couldn't open $ebs_log_binary=$!" );
		binmode EBS;
		undef $/;
		$total_content = unpack("H*",<EBS>);
		close EBS;
		$/ = "\n";

		if( length( $total_content ) == 0 )	{
			print $OUT "$prog: Input log file is empty\n";
		}

		&parse_content();

		$end_time = localtime();
		foreach my $k (keys %event_counter_tab){
			$total_nbr_events = $total_nbr_events + $event_counter_tab{$k};
		}

		$total_nbr_events = $total_nbr_events + $nbr_unknown_event;
		print $OUT "###STATS###\n";
		print $OUT "Processing start time=$start_time\n";
		print $OUT "Processing end time=$end_time\n";
		foreach my $k (keys %event_counter_tab)
		{
			print $OUT "Number of  ".$k."=".$event_counter_tab{$k}."\n";
			$event_counter_tab{$k} = 0;
		}
		print $OUT "Number of unknown event=$nbr_unknown_event\n";
		print $OUT "Total number of events=$total_nbr_events\n";
		if ($mode eq "summary" ) {
			foreach my $k (keys %counters)
			{
				print_stats($k) if ($k =~ /\w/);
				delete $counters{$k};
				delete $cc_stats{$k};
				delete $sub_cc_stats{$k};
			}
		}elsif ($mode eq "counter" ) {
			print_counters();
		}
	}
	if ($mode eq "counter" && exists $opts{'d'} && $c_total > 1) {
		print_counters_summary();
	}
	if ($nbr_hit > 40) {
		print STDERR "  Done!" if ( exists $opts{'o'});
		print STDERR "\n";
	}
}

#####################################################
# Parse the content of each event.
#####################################################
sub parse_content
{
	my $k = 0;
	my $type;
	my $error_type;
	my $termination_cause;
	my $event_id;
	my $readp = 0;
	my $p_event_name = undef;
	my $total_content_length = length ($total_content);
        my $last_time = time();
        my $curr_time = time();

	while( $total_content_length - $readp > 0 )
	{
                $curr_time = time();
                if ($curr_time - $last_time > 4 ) {
                        print STDERR ".";
                        $last_time = $curr_time;
                        $nbr_hit++;
                }

		$this_record_length = oct( "0x" . substr( $total_content, $readp, 4 ) );
		$type = oct( "0x" . substr( $total_content, $readp+4, 2 ) );
                $this_record_content = substr( $total_content, $readp, 2 * $this_record_length );
		$readp = $readp + 2 * $this_record_length;

		#Read record header
		if( $type == 0 ){
			$year = oct( "0x" . substr( $this_record_content, 10, 4 ) );
			$month = oct( "0x" . substr( $this_record_content, 14, 2 ) );
			if( $month < 10 )	{
				$month = "0" . $month;
			}
			$day = oct( "0x" . substr( $this_record_content, 16, 2 ) );
			if( $day < 10 ){
				$day = "0" . $day;
			};
			$hour = oct( "0x" . substr( $this_record_content, 18, 2 ) );

                        if($hour < 10){
                                $hour = "0" . $hour;
                        }

                        $minute = oct( "0x" . substr( $this_record_content, 20, 2 ) );
			if( $minute < 10 )	{
				$minute = "0" . $minute;
			}
			$second = oct( "0x" . substr( $this_record_content, 22, 2 ) );
			if( $second < 10 )	{
				$second = "0" . $second;
			}
			$FFV = oct( "0x" . substr( $this_record_content, 6, 2 ) );
			$FIV = oct( "0x" . substr( $this_record_content, 8, 2 ) );

			if ($FFV != $FFV_XML || $FIV != $FIV_XML) {
				print "\nWarning: Version of log file and ebm.xml mismatch!!\n";
				print "FFV and FIV in log: $FFV,$FIV; in ebm.xml:$FFV_XML,$FIV_XML\n";
				print "Parse result maybe incorrect!\n\n";
			}

		}
		#Read record payload
		elsif( $type == 1 ){
			$this_record_content_BIT = unpack("B*",pack("H*",$this_record_content));
			$this_record_content_BIT_index = 24;
			$event_id = oct( "0b" . substr( $this_record_content_BIT, 24, 8 ) );
			$event_record{'event_result'} = oct( "0b" . substr( $this_record_content_BIT, 32, 2 ) );

			if (exists $all_events->{$event_id}){
				$p_event_name = $all_events->{$event_id}{name};
				$event_counter_tab{$p_event_name}++;

				# Filter unsuccessful Events (reject/abort/ignore Events),
				next if ($unsuccessful eq "true" && ( $event_record{'event_result'} !~ /$unsuccessful_pattern/))  ;

				# Filtered Event or does not filter on Event, then decode this Event
				if( (($decode_all eq "false") && (1 == $event_list_tab{$event_id})) || ($decode_all eq "true"))	{
					decode_event($event_id);
				}
			}else{
				print STDERR "\nERROR: Unsupported Event ID '$event_id' !!!\n\n";
				exit 1;
			}
		}
		#Read error record
		elsif( $type == 2 ){
			$hour = oct( "0x" . substr( $this_record_content, 6, 2 ) );
                        if($hour < 10){
                                $hour = "0" . $hour;
                        }
                        $minute = oct( "0x" . substr( $this_record_content, 8, 2 ) );
			if( $minute < 10 )	{
				$minute = "0" . $minute;
			}
			$second = oct( "0x" . substr( $this_record_content, 10, 2 ) );
			if( $second < 10 )	{
				$second = "0" . $second;
			}
			$error_type = oct( "0x" . substr( $this_record_content, 12, 2 ) );
		}
		#Read record footer
		elsif( $type == 3 ){
			$termination_cause = oct( "0x" . substr( $this_record_content, 6, 2 ) );
		}
		#Unsupported Record Type
		else{
			print $OUT "\nERROR: Unsupported Record Type '$type' !!!\n\n";
			exit 1;
		}

                if ($mode eq "detail" ){
			&print_out($type,$error_type,$termination_cause,$event_id);
			#Clear some entries for next loop. Necessary for filtering.
			delete $event_record{'apn'} if ( exists $event_record{'apn'} )	;
			delete $event_record{'rat'} if ( exists $event_record{'rat'} ) ;
			delete $event_record{'imeisv'} if ( exists $event_record{'imeisv'} ) ;
			delete $event_record{'millisecond'} if ( exists $event_record{'millisecond'} )	;
                }elsif ($mode eq "summary" ){
			$p_event_name .= "_$event_record{'rat'}" if (exists $event_record{'rat'});
			$p_event_name = lc($p_event_name);
			$counters{$p_event_name}{$event_record{'event_result'}}++;
			$cc_stats{$p_event_name}{$event_record{'cause_code'}}++;
			$sub_cc_stats{$p_event_name}{$event_record{'cause_code'}}{$event_record{'sub_cause_code'}}++;
			delete $event_record{'rat'} if ( exists $event_record{'rat'} )	;
			$p_event_name = undef;
                }elsif ($mode eq "counter" ){
                        &handle_counter();
                }

		$event_str = "";
	}
}

sub handle_counter
{
	if($event_record{'event_id'} eq "l_attach" && $event_record{'event_result'} eq "success"){
		$l_attach_times += 1;
		$l_attach_duration += $event_record{'duration'};
		my $time_stamp = sprintf("%02s:%02s:%02s",$event_record{'time_hour'},$event_record{'time_minute'},$event_record{'time_second'});
		$l_attach_first_time = $time_stamp if ( $l_attach_first_time eq "");
		$l_attach_last_time = $time_stamp;
	}elsif($event_record{'event_id'} eq "l_service_request"){
		my $tai="$event_record{'mcc'}-$event_record{'mnc'}-$event_record{'tac'}";
		if(($event_record{'paging_attempts_enb'} != 0) || ($event_record{'paging_attempts_ta'} != 0)){
			if(defined $l_serv_req{$tai}{'att'}){
				$l_serv_req{$tai}{'att'} += 1;
			}else{
				$l_serv_req{$tai}{'att'} = 1;
			}
			if($event_record{'event_result'} eq "success" && $event_record{'paging_attempts'} == 1){
				if(defined $l_serv_req{$tai}{'FirSucc'}){
					$l_serv_req{$tai}{'FirSucc'} += 1;
				}else{
					$l_serv_req{$tai}{'FirSucc'} = 1;
				}
			}
			elsif($event_record{'event_result'} eq "success" && $event_record{'paging_attempts'} > 1){
				my $tmp_sum =$event_record{'paging_attempts_enb'} + $event_record{'paging_attempts_ta'};
				if($tmp_sum >= $event_record{'paging_attempts'}){
					if(defined $l_serv_req{$tai}{'SecSucc'}){
						$l_serv_req{$tai}{'SecSucc'} += 1;
					}else{
						$l_serv_req{$tai}{'SecSucc'} = 1;
					}
				}
			}
		}
	}
	delete $event_record{'event_id'} if ( exists $event_record{'event_id'} )  ;
}

#####################################################
# Push the IE info into array.
#####################################################
sub build_ie_format
{
	my ($eventId, $name, $type, $len, $useValid, $optional, $seqLen, $level) = @_;

	if((exists $ie_types->{$type}) ){
		$name = $type if (! $name);
		my $childNum = 0;
		if  ($#{$ie_types->{$type}} > 0) {
			push(@{$all_events->{$eventId}{ies}},
					{
						name	=>	$name,
						elName	=>	$name,
						type		=>	$type,
						len		=>	$len,
						level		=>	$level,
						isLeaf	=>	0,
						useValid	=>	$useValid,
						optional	=>	$optional,
						seqLen	=>	$seqLen,
						childNum =>	$#{$ie_types->{$type}}
					}
			);
			$childNum += 1;
		}


		for my $i ( 0 .. $#{$ie_types->{$type}}) {
			my $elem = $ie_types->{$type}->[$i];

			if ($elem->{isLeaf} != 1){
	 			$childNum += build_ie_format($eventId, $elem->{name}, $elem->{type},  $elem->{len}, $elem->{useValid}, $elem->{optional}, $elem->{seqLen}, $level + 1);
	 		} else{
				push(@{$all_events->{$eventId}{ies}},
						{
							name	=>	$elem->{name},
							elName	=>	$name,
							type		=>	$elem->{type},
							len		=>	$elem->{len},
							level		=>	$level,
							isLeaf	=>	1,
							useValid	=>	$useValid,
							optional	=>	$optional,
							seqLen	=>	$seqLen,
							childNum =>	0
						}
				);
				$childNum += 1;
	 		}
	 	} #for

		if ($#{$ie_types->{$type}} > 0) {
			my $ind = $#{$all_events->{$eventId}{ies}};
			my $elem = $all_events->{$eventId}{ies}->[$ind -$childNum +1];
			$elem->{childNum} = $childNum -1;
		}

	 	return $childNum;
	 }else{
		print STDERR "\nERROR: unknown type '$type' for IE '$name' !!!\n\n";
		exit 1;
	 }
}

#####################################################
# Build all the Event format.
#####################################################
sub build_event_format
{
	my ($events) = @_;
	foreach my $eventId (keys %{$events}){		#all events
		for my $i ( 0 .. $#{$events->{$eventId}}) {	#all ies
			my $elem = $events->{$eventId}->[$i];
			my $childNum = build_ie_format($eventId, $elem->{name},$elem->{type},0, $elem->{useValid},$elem->{optional},$elem->{seqLen},1);
		}
	}
}

#####################################################
# Decode function for each IE type.
#####################################################
sub decode_ie_type
{
	my ($elem, $useValid) = @_;
	my $result;

	print "    " x ($elem->{level}). "         : type_name($elem->{name}), IE_name($elem->{elName}),type($elem->{type}),level($elem->{level}), len($elem->{len}, useValid($useValid))\n" if ($opts{'G'} == 2);

	#If summary mode, just parse the concerned IEs
	if (($mode eq "summary" ) && ($elem->{name} !~ /cause_code|cause_prot|event_/)
		&& ($elem->{type} =~ /uint|enum|ipaddress|bcd/)){
		$this_record_content_BIT_index = $this_record_content_BIT_index + $elem->{len};
		return;
	}

    if ($elem->{name} =~ /^pdp_status$/) {
        $result = decode_bit_string($elem->{len});
        $event_record{$elem->{elName}} = $result;
    }elsif ($param_mode eq "all" or $usechild==1 or exists($use_param{$elem->{elName}."\n"}) or $elem->{type} eq 'dnsname' or $elem->{type} eq 'bytearray') {  #if the param needs to be used  $elem->{level}>1
        if(exists $decode_types{$elem->{type}}){
                $result = $decode_types{$elem->{type}}->($elem->{len},$elem->{name}); #decode
                $event_record{$elem->{elName}} = $result;
        }else{
                print STDERR "\nERROR: unknown type '$elem->{type}' for '$elem->{name}' !!!\n\n";
                exit 1;
        }
    }else{ #skip decoding params not needed
         $this_record_content_BIT_index = $this_record_content_BIT_index + $elem->{len};
         return;
	}

	if ($elem->{elName} =~ /^sub_cause_code$/ && exists $cause_code{'sub'}{$result}){
        	$result = $cause_code{'sub'}{$result}{'name'};
		$event_record{$elem->{elName}} = $result;
        }elsif ($elem->{elName} =~ /^bearer_cause$/ && exists $cause_code{'bearer'}{$result}){
                $result = $cause_code{'bearer'}{$result}{'name'};
		$event_record{$elem->{elName}} = $result;
        }elsif ($elem->{elName} =~ /^previous_s1_release_cause$/ && exists $cause_code{'s1ap'}{$result}){
                $result = $cause_code{'s1ap'}{$result}{'name'};
		$event_record{$elem->{elName}} = $result;
        }

	if(!$pr_all){
		if ($elem->{elName} =~ /^cause_code$/){
                	$result = uc($elem->{elName});
		}

		if($elem->{elName}) {
			#$result = "    " x ($elem->{level} -1)."$elem->{elName} = $result\n" ;
			$result = "    " x ($elem->{level} -1)."$elem->{elName} = ". anonymize($elem->{elName},$result). "\n";
		}else{
			#$result = "    " x ($elem->{level} -1)."$elem->{name} = $result\n" ;
			$result = "    " x ($elem->{level} -1)."$elem->{name} = ". anonymize($elem->{name},$result). "\n";
		}
	}
	else{
	    ## $pr_all
	    if (($md5_encrypt eq "true") && ($useValid !=0)) {
                 $result = "undefined";
            }

	    ## legacy logic, don't ask why
            if ($elem->{elName} =~ /^imsi$/i || $elem->{elName} =~ /^imeisv$/i) {
                 $all_ies->{$elem->{elName}} = $result;
                 $result == "";
            }
	}
	#elsif ($elem->{elName} =~ /^imsi$/i || $elem->{elName} =~ /^imeisv$/i) {
        #	$all_ies->{$elem->{elName}} = $result ;
	#	$result == "";
	#}

	$event_str .= $result if ($useValid == 0);

	print "    " x ($elem->{level}). "         : result($result)\n" if ($opts{'G'} == 2);

	return $result."-";
}

#####################################################
# Decode IE with tag 'seqmaxlen'
#####################################################
sub decode_seqLen
{
	my ($event_id, $index,$length,$last_useValid) = @_;
	my ($result, $value ) = ("","");
	my $hit = 0;
	my $with_filter = "false";


	my $elem = $all_events->{$event_id}{ies}->[$index -1];
	$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;

	for (my $i = 0; $i < $length; $i++) {
		$elem = $all_events->{$event_id}{ies}->[$index + $i];

		if ($opts{'G'} == 3) {
			print "($index + $i):\t" . "   " x ($elem->{level}-1). "IE_name($elem->{name}),type($elem->{type}),len($elem->{len}),level($elem->{level}),";
			print "usevalid($elem->{useValid}),optional($elem->{optional}),seqLen($elem->{seqLen}),isLeaf($elem->{isLeaf}),childNum($elem->{childNum})\n";
		}
		$result = "";

		$last_useValid = 0 if ($elem->{level} <= $last_useValid);

		if (defined $elem->{useValid}) {
			my $usevalid = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 1 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 1;

			if ($usevalid == 1 && $last_useValid == 0) {
				$last_useValid = $elem->{level};
			}

			if ($elem->{isLeaf} != 1){
	 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
	 		} else{
	 			$result = decode_ie_type($elem, $last_useValid);
	 		}
		#containing attribute "optional"
		}elsif (defined $elem->{optional}) {
			my $optional = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 1 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 1;
			if( $optional == 1 )	{
				if ($pr_all == 1 && $elem->{isLeaf} == 1) {
					$result = "undefined-" ;
				}else {
					$event_str .=  "    " x ($elem->{level} -1)."$elem->{name} = undefined\n";
				}
			} else {
				if ($elem->{isLeaf} != 1){
		 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
		 		} else{
		 			$result = decode_ie_type($elem, $last_useValid);
		 		}
			}

		#containing attribute "seqMaxLen"
		}elsif (defined $elem->{seqLen}) {
			my $seq_length = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 8 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 8;
			while ($seq_length > 0)
			{
				if ($elem->{isLeaf} != 1){
		 			$result = decode_seqLen($event_id, $index + $i + 1,$elem->{childNum},$last_useValid) ;
		 		} else{
		 			$result = decode_ie_type($elem, $last_useValid);
		 		}
				if ($pr_all == 1) {
					$result =~ s/-$//;
					$value .= "$result\/";
				}
				$seq_length = $seq_length - 1;
			}
			$value =~ s/\/$//;
			$i += $elem->{childNum};

		#there is no attribute
		}else{
			if ($elem->{isLeaf} != 1){
	 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
	 		} else{
	 			$result = decode_ie_type($elem, $last_useValid);
	 		}
		}
		$value .= $result if ($pr_all == 1 );
		if (exists $filters{$elem->{elName}}){
			$with_filter = "true";
			if ($elem->{isLeaf} == 1){
				$hit = filter_ie($elem->{elName}, $event_record{$elem->{elName}});
			}
		}
	}
	return ($value,$hit,$with_filter);
}

#####################################################
# Decode one Event.
#####################################################
sub decode_event
{

	my ($event_id) = @_;
	my ($result, $value, $last_elName,$useValid,$last_useValid) = ("",undef,undef,undef,0);

	$filter_hit = 1;
	for (my $i = 0; $i <= $#{$all_events->{$event_id}{ies}}; $i++) {	#all ies
		my $elem = $all_events->{$event_id}{ies}->[$i];
		if ($elem->{level}==1){
            if($elem->{elName} =~ /header$/ or exists($use_param{$elem->{elName}."\n"})) {
                $usechild=1;   #child needs to be decoded
            }
            else {
                $usechild=0;
            }
        }

		if ($opts{'G'} == 3) {
			print "$i:\t" . "   " x ($elem->{level} -1). "IE_name($elem->{name}),type($elem->{type}),len($elem->{len}),level($elem->{level}),";
			print "usevalid($elem->{useValid}),optional($elem->{optional}),seqLen($elem->{seqLen}),isLeaf($elem->{isLeaf}),childNum($elem->{childNum})\n";
		}

		if ( $this_record_content_BIT_index > $this_record_length * 8) {
			$event_str .="Confirm version! More IEs in ebm.xml, which not encoded: $elem->{name} ...\n\n";
			return;
		}

		$last_useValid = 0 if ($elem->{level} <= $last_useValid);

		if ($pr_all == 1 && $elem->{level} == 1 ){
			#print "$elem->{name},$elem->{level}:value:$result,last_elName:$last_elName,\n";

		 	if ($last_elName) {
				$result =~ s/-$//;
				$all_ies->{$last_elName} = $result;
				$result = undef;
			}

			if (! $elem->{elName}){
				$last_elName = $elem->{type};
			}else{
				$last_elName = $elem->{elName};
			}

		}

		if (defined $elem->{useValid}) {
			my $usevalid = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 1 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 1;

			if ($usevalid == 1 && $last_useValid == 0) {
				$last_useValid = $elem->{level};
			}

			if ($elem->{isLeaf} != 1){
	 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
	 		} else{
	 			$result .= decode_ie_type($elem, $last_useValid);
	 		}

		#containing attribute "optional"
		}elsif (defined $elem->{optional}) {
			my $optional = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 1 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 1;
			if( $optional == 1 ) {
				if ($pr_all == 1 && $elem->{isLeaf} == 1) {
					$result .= "undefined-" ;
				}else {
					$event_str .=  "    " x ($elem->{level} -1)."$elem->{elName} = undefined\n";
				}
			} else {
				if ($elem->{isLeaf} != 1){
		 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
		 		} else{
		 			$result .= decode_ie_type($elem, $last_useValid);
		 		}
			}

		#containing attribute "seqMaxLen"
		}elsif (defined $elem->{seqLen}) {
			my $seq_length = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, 8 ) );
			$this_record_content_BIT_index = $this_record_content_BIT_index + 8;
			my $hit_in_attribute=0;
			my $with_filter_in_attribute="false";
			while ($seq_length > 0)
			{
				my $tmp = "";
				my $hit_in_sub_attribute = 0;
				my $with_filter_in_sub_attribute = "false";
				if ($elem->{isLeaf} != 1){
					($tmp,$hit_in_sub_attribute,$with_filter_in_sub_attribute) = decode_seqLen($event_id, $i+1,$elem->{childNum},$last_useValid) ;
				} else{
					$tmp = decode_ie_type($elem, $last_useValid);
				}

				if ($pr_all == 1) {
					$tmp =~ s/-$// ;
					$result .= $tmp. "|";
				}

				$seq_length = $seq_length - 1;
				$hit_in_attribute |= $hit_in_sub_attribute;
				if ($with_filter_in_sub_attribute  eq "true") {
					$with_filter_in_attribute="true";
				}
			}
			if ($with_filter_in_attribute eq "true"){
				$filter_hit &= $hit_in_attribute;
			}
			$result =~ s/\|$//;
			$i += $elem->{childNum};
		#there is no attribute
		}else{
			if ($elem->{isLeaf} != 1){
	 			$event_str .= "    " x ($elem->{level} -1)."$elem->{elName}:\n" ;
	 		} else{
	 			$result .= decode_ie_type($elem, $last_useValid);
	 		}
		}

		#if ($pr_all == 1) {$value .= $result if ($elem->{isLeaf} == 1);print "[$elem->{elName}:$value]\n";}

		if ((exists $filters{$elem->{elName}} ) && $elem->{isLeaf} == 1){
			$filter_hit &= filter_ie($elem->{elName}, $event_record{$elem->{elName}});
			if (!$filter_hit ) {
				if ($pr_all == 1) {
					foreach my $key (sort keys %{$all_ies}) {
						$all_ies->{$key} = "";
					}
				}
				return;
			}
 		}
	}

	if ($pr_all == 1 && $last_elName){
		$result =~ s/-$//;
		$all_ies->{$last_elName} = $result;
		$result = undef;
	}

	#update cause_code
	my ($cause,$protocol_type) = ($event_record{cause_code},"");

	if ($all_events->{$event_id}{name} =~/^l_/i){
		$protocol_type = $event_record{l_cause_prot_type};
	}else{
		$protocol_type = $event_record{cause_prot_type};
	}

	if (exists $cause_code{$protocol_type}{$cause}) {
		$cause =  $cause_code{$protocol_type}{$cause}{'name'};
                $event_record{cause_code} = $cause;
	}

	$event_str =~ s/CAUSE_CODE/$cause/m;
	$all_ies->{cause_code} = $cause ;

}

#####################################################
# Decode IE of BCD type.
#####################################################
sub bcd_coding
{
	my $in = $_[0];
	my $out = "";
	while( length( $in ) > 0)
	{
		$out = $out . substr( $in, 1, 1 ) . substr( $in, 0, 1 );
		$in = substr( $in, 2 );
	}

	if( not( $out =~ m/^[fF]+$/ ) )
	{
		$out =~ s/[fF]+//;
	}

	return $out;
}

#####################################################
# Decode IE of uint type.
#####################################################
sub decode_uint
{
	my ($len,$name)=@_;
	my $uint_val = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, $len) );
	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;
	$uint_val = $cause_code{bearer_cause}{$uint_val}  if ($name eq "bearer_cause" && exists $cause_code{bearer_cause}{$uint_val} );
	return $uint_val;
}

#####################################################
# Decode IE of enum type.
#####################################################
sub decode_enum
{
	my ($len,$name)=@_;
	my $enum_val = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, $len) );
	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;
	if (exists $enums->{$name}->{$enum_val}) {
		return $enums->{$name}->{$enum_val};
	}else {
		return $enum_val;
	}
}

#####################################################
# Decode IE of bytearray type.
#####################################################
sub decode_bytearray
{
	my($len)=@_;

	my $el_len = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) );

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;

	$el_len = 8 * $el_len;

	my $nr_of_bits_to_next_byte = 8 - $this_record_content_BIT_index % 8;
	if ( $nr_of_bits_to_next_byte == 8 )	{
		$nr_of_bits_to_next_byte = 0;
	}
	$this_record_content_BIT_index = $this_record_content_BIT_index + $nr_of_bits_to_next_byte;


	my $in = unpack("H*",pack("B*",substr( $this_record_content_BIT, $this_record_content_BIT_index, $el_len ) ) );
	(my $bytearray_val_ascii = $in) =~ s/([a-fA-F0-9]{2})/chr(hex $1)/eg;

	$this_record_content_BIT_index = $this_record_content_BIT_index + $el_len;

	return  $bytearray_val_ascii;
  }

#####################################################
# Decode IE of ipaddress type.
#####################################################
sub decode_ipaddress
{
	my ($len) = @_;

	my @ipv4_val = unpack( "(C2)*", pack( "B*", substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) );

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;

	return join('.', @ipv4_val);
}

#####################################################
# Decode IE of ipaddress_v4 type.
#####################################################
sub decode_ipaddressv4
{
	my ($len) = @_;

	my @ipv4_val = unpack( "(C2)*", pack( "B*", substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) );

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;

	return join('.', @ipv4_val);
}

#####################################################
# Decode IE of ipaddress_v6 type.
#####################################################
sub decode_ipaddressv6
{
	my ($len) = @_;

	my @ipv6_arr = unpack("(H4)*",pack("B*",substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) );

	my $ipv6_val = join(':', @ipv6_arr);

	$ipv6_val =~ s/:0{1,3}/:/g;
	$ipv6_val =~ s/^0{1,3}//g;

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;
	return $ipv6_val;
}

#####################################################
# Decode IE of TBCD type.
#####################################################
sub decode_tbcd
{
	my ($len) = @_;
	my $tbcd_val = unpack( "h*", pack( "B*", substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) );
	$tbcd_val =~ tr/[fF]+//d	if( not( $tbcd_val =~ m/^[fF]+$/ ) );

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;

	return $tbcd_val;
}

#####################################################
# Decode IE of dnsname type.
#####################################################
sub decode_dnsname
{
	my ($len) = @_;

	my $apn_length = oct( "0b" . substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) );
	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;
	$len = 8 * $apn_length;
	#padding, moving start-of-apn to next byte
	my $nr_of_bits_to_next_byte = 8 - $this_record_content_BIT_index % 8;
	if ( $nr_of_bits_to_next_byte == 8 )
	{
		$nr_of_bits_to_next_byte = 0;
	}

	$this_record_content_BIT_index = $this_record_content_BIT_index + $nr_of_bits_to_next_byte;
	my $in = unpack("H*",pack("B*",substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) );

	my $dnsname_val = "";
	my $index = 0;
	while( $index < length( $in ) )
	{
		my $length_of_one_section = 2 * oct( "0x" . substr( $in, $index, 2 ) );
		my $one_section = substr( $in, 2 + $index, $length_of_one_section );

		(my $one_section_ascii = $one_section) =~ s/([a-fA-F0-9]{2})/chr(hex $1)/eg;
        (my $one_section_ascii_nl = $one_section_ascii) =~ s/[\x00-\x1f\x3b\x7f-\x9f]+/<non-printable-character>/g;
        $dnsname_val = $dnsname_val . $one_section_ascii_nl . ".";

		$index = $index + $length_of_one_section + 2;
	};

	#remove end dot
	$dnsname_val = substr( $dnsname_val, 0, length( $dnsname_val ) - 1);
	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;
	return $dnsname_val;
}

#####################################################
# Decode IE of IBCD type.
#####################################################
sub bcd_coding__3hex
{
	my $in = $_[0];
	my $out = substr( $in, 2, 1 ) . substr( $in, 1, 1 ) . substr( $in, 0, 1 );
	$out =~ s/[fF]+//;
	return $out;
}
sub decode_ibcd
{
        my ($len) = @_;

	my $ibcd_val = bcd_coding__3hex( unpack("H*",pack("B*",substr( $this_record_content_BIT, $this_record_content_BIT_index, $len ) ) ) );

	$this_record_content_BIT_index = $this_record_content_BIT_index + $len;

	return $ibcd_val;
}

#####################################################
# Decode bit string type
# example: 1001 0100 --> [3,5,8]
# Used for PDP STATUS
#####################################################
sub decode_bit_string
{
    my ($len)=@_;
    my ($result, $i) = ("[]",0);
    my $tmp_string = substr( $this_record_content_BIT, $this_record_content_BIT_index, $len);
    $this_record_content_BIT_index = $this_record_content_BIT_index + $len;
    for ($i=0; $i < $len; $i++) {
        if (substr($tmp_string, $len - $i - 1, 1) eq "1") {
            $result .= $i. ",",
        }
    }
    $result =~ s/\[\](.*),$/[$1]/;

    return $result;
}


#####################################################
# Print out the parse result.
#####################################################
sub print_out
{
	my $type = $_[0];
	my $error_type = $_[1];
	my $termination_cause = $_[2];
	my $event_id = $_[3];
	my $skip_next = "false";
        my $event_time = "time = $year-$month-$day ";
        my $event_time_millisecond = "000";

	print "print_out: type ($type), filter_hit($filter_hit)\n" if ($opts{'G'} == 2);
	if( $type == 0 )
	{
		if ($pr_all ==1 )
		{
                        # TR : SGSN00089351 - Introducing new option "-l -T"
                        # to display date along with event Time in parse event data.
                        my $string="";
                        if (exists $opts{'T'}) {
                                $string = "event_id${delimiter}event_result${delimiter}date${delimiter}time${delimiter}millisecond${delimiter}duration${delimiter}";
                        }else{
                                $string = "event_id${delimiter}event_result${delimiter}time${delimiter}millisecond${delimiter}duration${delimiter}";
                        }
			foreach my $key (sort keys %{$all_ies}) {
				$string .= "$key${delimiter}" if ($key !~ /header$/ and ($param_mode eq "all" or exists($use_param{$key."\n"})));
			}
			print $OUT "$string\n";
		} else {
			print $OUT "\n###HEADER###\n";
                        print $OUT "date=$year-$month-$day\n";
			print $OUT "time=$hour:$minute:$second\n";
			print $OUT "FFV=$FFV\n";
			print $OUT "FIV=$FIV\n\n";
		}
	}
	elsif( $type == 1 )
	{
		my $filter_length = @filters;

		# Old logic, we only execute filter here; to filter earlier (faster), some moved to "decode_event".
		if (  $filter_length != 0 ) {
			# whether this Event contain the Filtered IEs, if not then skip;
			$filter_hit = filter_event();
		}else{
			$filter_hit=1;
		}
		print "        filter_hit($filter_hit)\n" if ($opts{'G'} == 2);
		if ($filter_hit == 1 ){
			if( (($decode_all eq "false") && (1 == $event_list_tab{$event_id})) || ($decode_all eq "true"))	{
				if ($pr_all == 1){
					&print_all_ies;
				}else{
					if ($delimiter eq "\n")	{
						print $OUT "======EVENT======\n";
			                }
                                         if(exists $opts{'T'})
                                        {
                                            if($event_str =~ /time_millisecond = (\d{1,3})/){
                                               $event_time_millisecond = $1;
                                               $event_str =~ s/ *time_millisecond = \d{1,3}\n//;
                                            }
                                            if($event_str =~ /time_hour = (\d{1,2}).*time_minute = (\d{1,2}).*time_second = (\d{1,2})/s){
                                               # Some EBM events at midnight might get reported in next cycle.
                                               # Since the events have only hh:mm:ss:mmm, in such cases
                                               # manually correcting the display date to previous date.
                                               $event_time = "time = ".&print_date_ies($1)." ";
                                               $event_time .= sprintf("%02s:%02s:%02s:%03s", $1,$2,$3,$event_time_millisecond);
                                               $event_str =~ s/time_hour.*time_minute.*time_second = \d{1,2}/$event_time/s;
                                           }
                                        }

                                        print $OUT $event_str;  #print out the event result
                                        print $OUT "\n";
				}
			}
		}else{
                        if ($pr_all == 1) {
                                foreach my $key (sort keys %{$all_ies}) {
                                        $all_ies->{$key} = "";
                                }
                        }
                }
	}
	elsif( $type == 2 ){
		print $OUT "\n###ERROR###\n";
		print $OUT "error_type=$error_type\n\n\n\n\n\n";
	}
	elsif( $type == 3 ){
		print $OUT "\n###FOOTER###\n";
		print $OUT "termination_cause=$termination_cause\n\n";
	};
}

#####################################################
# Print the result in table format (with -l option).
#####################################################
sub print_all_ies
{
    #header: ("event_id","event_result","time",["millisecond","duration"])
    my $string ="";

    # TR : SGSN00089351 - Introducing new option "-l -T"
    # to display date along with event Time in parse event data.
    my $header_str = "";

    if ($all_ies->{header} =~ /\w/)
    {
        $header_str = $all_ies->{header};
    } elsif ($all_ies->{l_header} =~ /\w/) {
        $header_str = $all_ies->{l_header};
    } elsif ($all_ies->{n_header} =~ /\w/) {
        $header_str = $all_ies->{n_header};
    } else {
        $header_str = "Unsupported Event HEAD info, please contact Ericsson for improvement";
    }

    my @header = split(/-/, $header_str);

    if (exists $opts{'T'} && exists $opts{'l'}) {
        my $date = &print_date_ies($header[2]);
        $string = "$header[0]${delimiter}$header[1]${delimiter}$date${delimiter}$header[2]:$header[3]:$header[4]${delimiter}$header[5]${delimiter}$header[6]${delimiter}";
    } else {
        $string = "$header[0]${delimiter}$header[1]${delimiter}$header[2]:$header[3]:$header[4]${delimiter}$header[5]${delimiter}$header[6]${delimiter}";
    }

	foreach my $key (sort keys %{$all_ies}) {
        $string .= anonymize($key,$all_ies->{$key})."${delimiter}" if ($key !~ /header$/ and ($param_mode eq "all" or exists($use_param{$key."\n"})));
		$all_ies->{$key} = "";
	}

	print $OUT "$string\n";
}

#####################################################
# anonymize the output (with -Y/-y option).
#
# imsi, msisdn, tac, imeisv and etc are encrypted with md5
#####################################################
sub anonymize
{
    my ($key, $value) = @_;

    # anonymous not enabled
    if($md5_encrypt eq "false") {
        return $value;
    }

    # fast return if no value need to be anonymized
    if ((length($value) == 0) ||
        ($value eq "undefined")) {
        return $value
    }

    if (($key eq "imsi") ||
        ($key eq "msisdn") ||
        ($key eq "a_msisdn") ||
        ($key eq "tac") || ($key eq "old_tac") ||
        ($key eq "macro_enodeb_id") ||
        ($key eq "home_enodeb_id") ||
        ($key eq "lac") || ($key eq "old_lac") ||
        ($key eq "rac") || ($key eq "old_rac") ||
        ($key eq "ipv4") || ($key eq "ipv6") ||
        ($key eq "sac") ||
        ($key eq "ggsn") ||
        ($key eq "ci") ||
        ($key eq "srvcc_target_rnc_id") ||
        ($key eq "target_rnc_id")) {
        ## direct encrypt
        $value=encrypt_md5($value,"true");
    }

    ## special encrypt
    if (($key eq "tai") ||
        ($key eq "old_tai")) {
        ## mcc-mnc-tac
        my @tai = split('-',$value);
        $tai[2]=anonymize("tac", $tai[2]);
        $value = join('-',@tai);
    }
    elsif (($key eq "rai") ||
           ($key eq "old_rai")) {
        ## mcc-mnc-lac-rac
        my @rai = split('-',$value);
        $rai[2]=anonymize("lac", $rai[2]);
        $rai[3]=anonymize("rac", $rai[3]);
        $value = join('-',@rai);
    }
    elsif (($key eq "location")) {
        ## mcc-mnc-lac-rac-ci-sac
        my @location = split('-',$value);
        $location[2]=anonymize("lac", $location[2]);
        $location[3]=anonymize("rac", $location[3]);
        $location[4]=anonymize("ci", $location[4]);
        $location[5]=anonymize("sac", $location[5]);
        $value = join('-',@location);
    }
    elsif (($key eq "old_location")) {
        ## old_mcc-old_mnc-old_lac-old_rac
        my @location = split('-',$value);
        $location[2]=anonymize("old_lac", $location[2]);
        $location[3]=anonymize("old_rac", $location[3]);
        $value = join('-',@location);
    }
    elsif (($key eq "pdn_info")) {
        ## ebi-ueipv4-ueipv6-pgwipv4-pgwipv6-scefipv4-scefipv6
        my @pdn_info = split('-',$value);
        $pdn_info[1]=anonymize("ipv4", $pdn_info[1]);
        $pdn_info[2]=anonymize("ipv6", $pdn_info[2]);
        $pdn_info[3]=anonymize("ipv4", $pdn_info[3]);
        $pdn_info[4]=anonymize("ipv6", $pdn_info[4]);
        $pdn_info[5]=anonymize("ipv4", $pdn_info[5]);
        $pdn_info[6]=anonymize("ipv6", $pdn_info[6]);
        $value = join('-',@pdn_info);
    }
    elsif (($key eq "one_pdp_info")) {
        ## nsapi-ggsn-msipv4-msipv6
        my @pdp_info = split('-',$value);
        $pdp_info[1]=anonymize("ipv4", $pdp_info[1]);
        $pdp_info[2]=anonymize("ipv4", $pdp_info[2]);
        $pdp_info[3]=anonymize("ipv6", $pdp_info[3]);

        $value = join('-',@pdp_info);
    }
    elsif (($key eq "s_gw") || ($key eq "old_s_gw") ||
           ($key eq "sgsn") || ($key eq "old_sgsn") || ($key eq "old_sgsn_ip") ||
           ($key eq "p_gw") ||
           ($key eq "ms_address") ||
           ($key eq "msc_on_sv") ||
           ($key eq "scef") ||
           ($key eq "iws_address") ||
           ($key eq "msc")) {
        ## ipv4-ipv6
        my @ipv4v6 = split('-',$value);
        $ipv4v6[0]=anonymize("ipv4", $ipv4v6[0]);
        $ipv4v6[1]=anonymize("ipv6", $ipv4v6[1]);
        $value = join('-',@ipv4v6);
    }
    elsif (($key eq "pdns")) {
        my @pdns = split('\|',$value);
        for (my $i = 0; $i < @pdns; $i++) {
            $pdns[$i] = anonymize("pdn_info", $pdns[$i]);
        }
        $value = join('|',@pdns);
    }
    elsif (($key eq "pdp_info")) {
        my @pdps = split('\|',$value);
        for (my $i = 0; $i < @pdps; $i++) {
            $pdps[$i] = anonymize("one_pdp_info", $pdps[$i]);
        }
        $value = join('|',@pdps);
    }
    elsif (($key eq "target_lai") ||
           ($key eq "srvcc_target_lai")) {
        ## mcc-mnc-lac
        my @lai = split('-',$value);
        $lai[2]=anonymize("lac", $lai[2]);
        $value = join('-',@lai);
    }
    elsif (($key eq "target_global_enb_id")) {
        ## mcc-mnc-macroenbid-homeenbid
        my @target_global_enb_id = split('-',$value);
        $target_global_enb_id[2] = anonymize("macro_enodeb_id", $target_global_enb_id[2]);
        $target_global_enb_id[3] = anonymize("home_enodeb_id", $target_global_enb_id[3]);
        $value = join('-',@target_global_enb_id);
    }
    elsif (($key eq "eci") ||
           ($key eq "old_eci")) {
        $value = "[".encrypt_md5(int($value/256),"false") ." ".encrypt_md5($value%256, "false"). "]";
    }
    elsif (($key eq "imeisv")) {
        ## encrypt SNR,
        my $snr;
        $snr = substr($value,8,6),
        $snr = encrypt_md5($snr, "false");
        $value="[". substr($value,0,8)." ". $snr. " ". substr($value,14). "]";
    }
    elsif (($key eq "ueid")) {
        ## mtmsi-imsi-imeisv
        my @ueid = split('-',$value);
        $ueid[1]=anonymize("imsi", $ueid[1]);
        $ueid[2]=anonymize("imeisv",$ueid[2]);
        $value = join('-',@ueid);
    }
    elsif (($key eq "msid")) {
        ## imsi-ptmsi-imeisv-msisdn
        my @msid = split('-',$value);
        $msid[0]=anonymize("imsi", $msid[0]);
        $msid[2]=anonymize("imeisv",$msid[2]);
        $msid[3]=anonymize("msisdn",$msid[3]);
        $value = join('-',@msid);
    }

    return $value;
}

#####################################################
# help function to get md5 value
#
# NOTE: 0, undefined is invalid
#####################################################
sub encrypt_md5
{
    my ($value, $bracket) = @_;

    if ((length($value) == 0) || ($value eq "undefined")) {
        return $value;
    }

    $md5_ctx->reset;
    $md5_ctx->add($value,$md5_salt);
    $value=$md5_ctx->hexdigest;
    $value=substr($value,0,$use_hash_len);

    if ($bracket eq "true") {
        $value = "[". $value ."]";
    }

    return $value;
}

# TR : SGSN00089351 - Introducing new option "-l -T"
# to display date along with event Time in parse event data.
sub print_date_ies
{
        my ($event_hour) = @_;
        # TR : SGSN00089510 - timelocal function month parameter range is 0 to 11.
        my $time = timelocal(0, 0, 0, $day, $month-1, $year);
        if ($event_hour - $hour >= $midnight_time_threshold) {
            $time -= 60 * 60 * 24;
        } elsif ($event_hour - $hour <(0-$midnight_time_threshold)) {
                 $time += 60 * 60 * 12;
        }
        my ($y, $m, $d) = (localtime $time)[5, 4, 3];
        my $date= sprintf("%4d-%02d-%02d", 1900 + $y, $m+1, $d);
}

########################################################################
sub print_stats
{
	my $event = $_[0];
	my $successful=exists($counters{$event}{'success'}) ? $counters{$event}{'success'} : 0;
	my $rejected=exists($counters{$event}{'reject'}) ? $counters{$event}{'reject'} : 0;
	my $aborted=exists($counters{$event}{'abort'}) ? $counters{$event}{'abort'} : 0;
	my $ignored=exists($counters{$event}{'ignore'}) ? $counters{$event}{'ignore'} : 0;
	my $total=$successful+$rejected+$aborted+$ignored;

	if ($total == 0) {
		return;
	}
	my $successful_ratio= sprintf("%.2f",100*$successful/$total);
	my $rejected_ratio= sprintf("%.2f",100*$rejected/$total);
	my $aborted_ratio= sprintf("%.2f",100*$aborted/$total);
	my $ignored_ratio= sprintf("%.2f",100*$ignored/$total);
	print $OUT "\n\n##################################################################################\n";
	print $OUT "  $event\n";
	print $OUT "##################################################################################\n";
	printf $OUT ("%-81s %-14s\n","total $event",":$total");
	printf $OUT ("%-81s %-14s %s\n","successful $event",":$successful","$successful_ratio%");
	printf $OUT ("%-81s %-14s %s\n","rejected $event",":$rejected","$rejected_ratio%");
	printf $OUT ("%-81s %-14s %s\n","aborted $event",":$aborted","$aborted_ratio%");
	printf $OUT ("%-81s %-14s %s\n","ignored $event",":$ignored","$ignored_ratio%");
	print $OUT "----------------------------------------------------------------------------------\n";
	print $OUT "  Number of events per cause code\n";
	print $OUT "----------------------------------------------------------------------------------\n";
	foreach my $cc (sort {$cc_stats{$event}{$b} <=> $cc_stats{$event}{$a}} keys %{$cc_stats{$event}}){
		my $text= $cc =~ /#(\d+)\((.*)\)/ ? "($2)" : "-";
		printf $OUT ("%-6s %-74s %s\n","cc#$1","$text",":$cc_stats{$event}{$cc}");
	}
	print $OUT "----------------------------------------------------------------------------------\n";
	print $OUT "  Number of sub cause codes per cause code\n";
	print $OUT "----------------------------------------------------------------------------------\n";
	foreach my $cc (sort {$cc_stats{$event}{$b} <=> $cc_stats{$event}{$a}} keys %{$cc_stats{$event}}){
		my $text= $cc =~ /#(\d+)\((.*)\)/ ? "($2)" : "-";
		print $OUT "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
		printf $OUT ("%-11s %-69s %s\n","cc#$1","$text",":$cc_stats{$event}{$cc}");
		print $OUT "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
		foreach my $sub_cc (sort {$sub_cc_stats{$event}{$cc}{$b} <=> $sub_cc_stats{$event}{$cc}{$a}} keys %{$sub_cc_stats{$event}{$cc}}){
			my ($text,$scc) =("-","-");
			if ( $sub_cc =~ /#(\d+)\((.*)\)/) {
				$scc = $1; $text = "($2)";
			}elsif( $sub_cc =~ /(\d+)/) {
				$scc = $1;
			}
			printf $OUT ("%-11s %-69s %s\n","sub_cc#$scc",$text,":$sub_cc_stats{$event}{$cc}{$sub_cc}");
		}
	}
}

sub print_counters
{
	if(exists $opts{'A'}){
		my $duration = $l_attach_duration/1000;
		my $average = $l_attach_duration;
		$average = $average/$l_attach_times if ($l_attach_times > 0);
		print $OUT "\nL_Attach Events\n";
		print $OUT "-" x 35 . "\n";
		printf $OUT ("%-23s: %-10s\n", "First time", "$year-$month-$day $l_attach_first_time");
		printf $OUT ("%-23s: %-10s\n", "Last  time", "$year-$month-$day $l_attach_last_time");
		printf $OUT ("%-23s: %-10s\n", "Number of success", $l_attach_times);
		printf $OUT ("%-23s: %-10s\n", "Total   duration (sec)", $duration);
		printf $OUT ("%-23s: %-10.0f\n", "Average duration (ms)", $average);
		print $OUT "\n";
		$l_attach_total_times += $l_attach_times;
		$l_attach_total_duration += $l_attach_duration;
		$l_attach_first_time1 = "$year-$month-$day $l_attach_first_time" if ($l_attach_first_time1 eq "");
		($l_attach_times,$l_attach_duration, $l_attach_first_time) = (0,0,"");

	}
	if(exists $opts{'S'}){
		my ($att, $firstsucc, $secsucc) = (0,0,0);
		my $sep = "-" x 79 . "\n";
		print $OUT "\nL_Service_Request Events\n";
		print $OUT $sep;
		printf $OUT ("%-19s %-19s %-19s %-19s\n","TA","MM.PagAtt","MM.FirstPagingSucc","MM.MultiPagingSucc");
		print $OUT $sep;
		foreach my $key(sort (keys %l_serv_req)){
			$l_serv_req{$key}{'att'} = 0 if ( ! exists   $l_serv_req{$key}{'att'});
			$l_serv_req{$key}{'FirSucc'} = 0 if (! exists   $l_serv_req{$key}{'FirSucc'});
			$l_serv_req{$key}{'SecSucc'} = 0 if (! exists   $l_serv_req{$key}{'SecSucc'});
			my $str = sprintf ("%-19s %-19s %-19s %-19s\n",$key,$l_serv_req{$key}{'att'},$l_serv_req{$key}{'FirSucc'},$l_serv_req{$key}{'SecSucc'});
			print $OUT "$str";

			$att += $l_serv_req{$key}{'att'};
			$firstsucc += $l_serv_req{$key}{'FirSucc'};
			$secsucc += $l_serv_req{$key}{'SecSucc'};

			#total number of all files
			if(defined $l_serv_req_total{$key}{'att'}){
				$l_serv_req_total{$key}{'att'} += $l_serv_req{$key}{'att'};
			}else{
				$l_serv_req_total{$key}{'att'} = $l_serv_req{$key}{'att'};
			}
			if(defined $l_serv_req_total{$key}{'FirSucc'}){
				$l_serv_req_total{$key}{'FirSucc'} += $l_serv_req{$key}{'FirSucc'};
			}else{
				$l_serv_req_total{$key}{'FirSucc'} = $l_serv_req{$key}{'FirSucc'};
			}
			if(defined $l_serv_req_total{$key}{'SecSucc'}){
				$l_serv_req_total{$key}{'SecSucc'} += $l_serv_req{$key}{'SecSucc'};
			}else{
				$l_serv_req_total{$key}{'SecSucc'} = $l_serv_req{$key}{'SecSucc'};
			}

			delete $l_serv_req{$key} if (exists $l_serv_req{$key});
		}
		print $OUT $sep;
		printf $OUT ("%-19s %-19s %-19s %-19s\n","Total",$att,$firstsucc,$secsucc);
		print $OUT "\n";
	}
}

sub print_counters_summary
{
	if(exists $opts{'A'}){
		my $duration = $l_attach_total_duration/1000;
		my $average = $l_attach_total_duration;
		$average = $average/$l_attach_total_times if ($l_attach_total_times > 0);
		print $OUT "#" x 40 . "\n";
		print $OUT "L_Attach Events Summary of all files\n";
		print $OUT "=" x 42 . "\n";
		printf $OUT ("%-23s: %-10s\n", "First time", $l_attach_first_time1);
		printf $OUT ("%-23s: %-10s\n", "Last  time", "$year-$month-$day $l_attach_last_time");
		printf $OUT ("%-23s: %-10s\n", "Number of success", $l_attach_total_times);
		printf $OUT ("%-23s: %-10s\n", "Total   duration (sec)", $duration);
		printf $OUT ("%-23s: %-10.0f\n", "Average duration (ms)", $average);
		print $OUT "\n";
	}
	if(exists $opts{'S'}){
		my ($att, $firstsucc, $secsucc) = (0,0,0);
		my $sep = "=" x 85 . "\n";
		print $OUT "#" x 50 . "\n";
		print $OUT "L_Service_Request Events Summary of all files\n";
		print $OUT $sep;
		printf $OUT ("%-19s %-19s %-19s %-19s\n","TA","MM.PagAtt","MM.FirstPagingSucc","MM.MultiPagingSucc");
		print $OUT $sep;
		foreach my $key(sort (keys %l_serv_req_total)){
			my $str = sprintf ("%-19s %-19s %-19s %-19s\n",$key,$l_serv_req_total{$key}{'att'},$l_serv_req_total{$key}{'FirSucc'},$l_serv_req_total{$key}{'SecSucc'});
			print $OUT "$str";

			$att += $l_serv_req_total{$key}{'att'};
			$firstsucc += $l_serv_req_total{$key}{'FirSucc'};
			$secsucc += $l_serv_req_total{$key}{'SecSucc'};
			delete $l_serv_req_total{$key} if (exists $l_serv_req_total{$key});
		}
		print $OUT $sep;
		printf $OUT ("%-19s %-19s %-19s %-19s\n","Total",$att,$firstsucc,$secsucc);
		print $OUT "\n";
	}
}
#####################################################
# Build filter list.
#####################################################
sub build_filter
{
	my $event_ids;
	if ( $unsuccessful eq "true" ) {
		foreach my $key (keys %{$enums->{event_result}}){
			my $result = $enums->{event_result}->{$key};
			$unsuccessful_pattern .= "^$key". '$|' if ($result !~ /^success$/i);
		}
		$unsuccessful_pattern =~ s/(.*)\|$/$1/;
	}
	push(@filters, "rat", $rat_pattern) if ( $rat eq "true");
	push(@filters, "cause_code", ${cause_code_pattern}) if ( $cause_code eq "true" )	;
	push(@filters, "sub_cause_code", ${sub_cause_code_pattern}) if ( $sub_cause_code eq "true" )	;
	push(@filters, "imsi", $imsi_pattern) if ( $imsi eq "true" );
	push(@filters, "imeisv", $imeisv_pattern) if ( $imeisv eq "true" );
	push(@filters, "apn", $apn_pattern) if ( $apn eq "true" );
	push(@filters, "time_second", ".*") if ( $opts{'D'} =~ /\d/ );

        if (($parameter ne "") && ($parameter_value ne "")) {
                $opts{'n'}=~ s/^\s+//;
                $opts{'v'}=~ s/^\s+//;
                my @par=split(/\s*\,\s*|\s+/,$opts{'n'});
                my @val=split(/\s*\,\s*|\s+/,$opts{'v'});
                if($#par != $#val) {
                        print "ERROR: Number of Parameter name and parameter value do not match! Exit ...\n";
                        exit 1;
                }
                for my $i (0..$#par)    {
                        push(@filters, "$par[$i]", $val[$i]) ;
                }
        }
	%filters = @filters;
        if ($opts{'e'}) {
                $opts{'e'}=~ s/^\s+//;
                my @arr=split(/\s*\,\s*|\s+/,$opts{'e'});
                foreach my $e (@arr)    {
                        &build_event_list($e);
                }
        }

	if ($opts{'G'} == 2) {
		print "Filters: \n";
		foreach my $k (keys %filters){
			print "key($k) -- value($filters{$k})\n";
		}
		print "key(event_result) -- value($unsuccessful_pattern)\n";
	}
}

#####################################################
# Filter the result (whether print out the event).
#####################################################
sub filter_event
{
	print "filter_event: filter_hit($filter_hit);" if ($opts{'G'} == 2);
	$filter_hit =0 if (exists $filters{'apn'} && (! exists $event_record{'apn'}));
	$filter_hit =0 if (exists $filters{'imeisv'} && (! exists $event_record{'imeisv'}));
    if (   ((exists $filters{'rat'}) && ($filters{'rat'} =~ /lte/) && ($event_record{'event_id'} !~ /^l_/))
        || ((exists $filters{'rat'}) && ($filters{'rat'} !~ /lte/) && ($event_record{'event_id'} =~ /^l_/))){
       $filter_hit = 0;
    }
	$filter_hit =0 if (exists $filters{$parameter} && (! exists $event_record{$parameter}));
        delete $event_record{$parameter};
	#print "result($filter_hit)\n" if ($opts{'G'} == 2);
	return $filter_hit;
}

sub filter_ie
{
	my ($key,$value) = @_;
	my $result = 1;
	$value = $1 if ( $key =~ /cause_code/ && $value =~ /#(\d+)\(/);
	$value = substr($value,0,8) if ( $key eq "imeisv" && $imeisv eq "true" )	;
	$result = 0 if (! ($value =~ /$filters{$key}/)) ;
	if ($opts{'D'} =~ /\d/ && $key eq "time_second") {
              my $time = sprintf("%02d:%02d:%02d",$event_record{'time_hour'},
                       $event_record{'time_minute'}, $event_record{'time_second'});
              if (($time ge $from_time) && ($time le $to_time)){
                    $result = 1;
              }else{
                    $result = 0;
              }
        }

	print "filter_ie: key($key), value($value), result($result)\n" if ($opts{'G'} == 2);
	return $result;
}

#####################################################
# Print out the warning.
#####################################################
sub sgsn_warning {
	my $snode=&get_sgsn_node;
	if($snode){
		#script is running on the sgsn node.
		print  "This script is not intended to be ran on the SGSN-MME, it might impact the capacity of the SGSN-MME. Are you sure you want to run the script (yes/no)? \n";
		my $in=<STDIN>;
		chomp($in);
		if($in =~ /y/i){
			return 0;
		}else{
			print  "Execution is canceled by the user. Exiting...\n";
			exit 0;
		}
	}
}

#####################################################
# Whether it's running on node or GTT.
#####################################################
sub get_sgsn_node {
        my $tec=qx(ps -ef|grep -v grep|grep gttRoot|awk '{print \$2}');
        my $tbox=qx(ps -ef|grep -v grep|grep tbox|awk '{print \$2}');
        if ($tec =~ /\d+/ || (-f "/etc/sgsninit/tecsas") || $tbox =~ /\d+/) {
              return 0;
        }elsif (-r "/tmp/DPE_SC/LoadUnits/ttx/int/bin/load_limit.pl") {
                  return 1;
        }
	return 0;
}

#####################################################
# This subroutine checks and returns the CPU load.
#####################################################
sub working
{
    my $now= time();
    if ( $sec != $now ){
        $sec=$now;
        print "$working[$wId]\b";
        $wId++;
        $wId= 0 if ( $wId >3);
    }
}
sub get_cpu_load {
    my $nr  = shift(@_);
    my $ret = 0;
    my $res = `cpu_stat -c 1  -n $nr || die "Cannot run 'cpu_stat  -c 1 -n $nr' - $!"`;

    foreach (split(/\n+/,$res)) {
      $ret += (split(/\s+/,$_))[2];
    }
    $ret = int($ret/($nr-1));
    return $ret;
}

#####################################################
# This subroutine checks CPU load and decides if the  script is allowed to start.
# If load caused by other processes > max_load, script pauses.
#  If load > max_load for to long, script terminates.
#####################################################
sub check_load {
	# read input parameters
	my $max_load   = shift(@_);
	my $iterations = shift(@_);
	my $flag       = shift(@_);
	my $load = 200;		# set start value greater than a 100%.
	my $i = 0;			# No of load check iterations.

	while ($load >= $max_load) {
		$load = get_cpu_load(5);
		if ($load > $max_load) {
			print ("Execution paused a few seconds due too high CPU load: $load% \n");
			sleep 3;		# Sleep until the load is lower than $max_load.
			$i++;
			if ($i > $iterations) { # After $iterations*3 sec's.
				print STDERR "ERROR: Script terminated due to persistent overload. \n";
				exit 1;
			}
		} else {
			if ($flag eq "initial") {
				print("CPU load check passed: load = $load% \n");
			}
			return;
		}
	}
}

sub cpu_load {
	print("Initial CPU Load Check...");
	check_load(40.0, 20, "initial"); # Max CPU load allowed
	print $OUT "\n";
  }

sub REAPER {
	my $child;
	my $count=10;
	my $child=1;
	while (($child >0) && ($count > 0)) {
		$child = waitpid(-1, &WNOHANG);
		$count--;
	}
	$SIG{CHLD} = \&REAPER;	# install *after* calling waitpid
}

#####################################################
# Main
#####################################################
#set nice
my $nice=10;
setpriority('PRIO_PROCESS',$$,$nice) or print("Cannot set priority for process - $!\n");
my $cpid;
my $snode=&get_sgsn_node;

my $opt_ok=getopts('hsulASTYFp:H:y:r:e:c:z:i:t:a:f:o:d:G:x:n:v:D:kC:L', \%opts);

my @opt_keys=keys %opts;

if(not $opt_ok){
     exit 1;
}
if (($#ARGV >=0) && ($#ARGV >= $#opt_keys)) {
     print "ERROR!\tUnknown option: @ARGV\n";
     exit 1;
}
if (exists $opts{h}) {
	usage;
	exit 0;
}
&get_opts();
if($param_mode eq "select"){
    open (PARAMFILE, "params.txt") or die ("Could not open param file");
    my @t = <PARAMFILE>;
    map {$use_param{$_}=1} @t;
}
&parse_ebm_xml($file);
parse_cause;
if (exists $opts{C} || exists $opts{L}) {
	print_cause_code;
	exit 0;
}
&build_filter();
redirect;

#####################################################
if ($snode) {
        if(!exists $opts{'k'}){
           sgsn_warning;
        }
	cpu_load;
	if ($cpid = fork) {
		# parent
		$SIG{CHLD} = \&REAPER;
		exec("/tmp/DPE_SC/LoadUnits/ttx/int/bin/load_limit.pl -s 1 -r 0.10 -p $cpid");
	} elsif (defined $cpid) {
		# child
		setpgrp(0,0);
		$SIG{CHLD} = 'IGNORE';
		process_ebs_log_files();
		#exit 0;
	} else {
		die "Can't fork: $!\n";
	}
} else {
	process_ebs_log_files();
}
if ($$OUT !~ /STDOUT/){
	close($OUT) || die "Could not flush buffer or close output file - $!";
}
exit 0;

