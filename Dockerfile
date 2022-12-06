FROM prodgitlab.vodafone.om:5050/shafique.kakati1/ebs_logs
MAINTAINER "shafique Kakati" shafiquekakati@gmail.com


RUN mkdir /data

WORKDIR /app
COPY * /app/

VOLUME /data


CMD ["/app/docker_entrypoint.sh"]
