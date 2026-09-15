####### coordinate descent algorithm ##########
cd.general <- function(X, y, exposure,Z,a0, beta, epsilon, max.iter, lambda, family, bInd, pf, 
                       pentype, gamma) {
  # pf: penalty factor all all components, 0 means no penalty
  X = cbind(X,1,exposure,Z)
  p = ncol(X)
  n = nrow(X)
  beta = c(beta,a0)
  pf = c(pf, rep(0,q+2))
  para.in = c(epsilon, max.iter, lambda, gamma)
  # cat('beta[1:10]', beta[1:min(length(beta),10)],'\n')
  if (family == 'gaussian') {
    out = .Fortran("cd_general_lin", X = as.double(X), y = as.double(y), p = as.integer(p), 
                   n = as.integer(n), beta = as.double(beta), pf = as.double(pf), 
                   pentype = as.integer(pentype), paraIn = as.double(para.in))
  } else if (family == 'binomial') {
    out = .Fortran("cd_general_bin", X = as.double(X), y = as.double(y), p = as.integer(p), 
                   n = as.integer(n), beta = as.double(beta), pf = as.double(pf), 
                   pentype = as.integer(pentype), paraIn = as.double(para.in))
  }
  return(list(a0 = out$beta[(p-q-1):p], beta = out$beta[-((p-q-1):p)]))
}


loglik <- function(X, y, beta, family) {
  link = as.vector(X %*% beta)
  n = length(y) 
  if (family == "gaussian") 
    return(n * log(mean((y - link)^2)))
  if (family == "poisson") 
    return(-2 * sum(exp(link) + 2 * y * link))
  if (family == "binomial") 
    return(2 * sum(log(1 + exp(link)) - y * link))
  
}

intertomain <- function(interNameList, p) {
  ### convert an interaction name list into the corresponding main effect for
  ### enforcing strong hierachy.  input: interNameList: interaction name list input:
  ### p: dimensionality
  mainInd = rep(0, p)
  for (i in 1:length(interNameList)) {
    interName = interNameList[[i]]
    pair = as.numeric(strsplit(interName, "X")[[1]][2:3])
    mainInd[pair[1]] = 1
    mainInd[pair[2]] = 1
  }
  return(which(mainInd == 1))
}

maintointer <- function(mainIndex) {
  ### expand main effects to possible interaction effects output: a list of
  ### interaction effects
  aa = outer(mainIndex, mainIndex, f <- function(x, y) {
    paste("X", x, "X", y, sep = "")
  })
  aa[lower.tri(aa, diag = TRUE)] = NA
  bb = as.vector(t(aa))
  bb = bb[!is.na(bb)]
  return(bb)
}


outercprod <- function(x, y) {
  x = as.matrix(x)
  y = as.matrix(y)
  do.call(cbind, lapply(1:ncol(x), function(i) x[, i] * y))
}

RAMP <- function(X, y,exposure, Z, family = "gaussian", penalty = "SCAD", gamma = NULL, inter = TRUE, 
                 hier = "Strong", eps = 1e-15, tune = "EBIC", penalty.factor = rep(1,ncol(X)), inter.penalty.factor = 1, lam.list, lambda.min.ratio, max.iter = 100, 
                 max.num, n.lambda = 100, ebic.gamma = 1, refit = TRUE, trace = FALSE) {
  ## hier = 'Strong', or 'Weak', strong or weak heredity.
  if (penalty == "SCAD" & is.null(gamma)) {
    gamma=3.7
  }
  if (penalty == "MCP" & is.null(gamma)) {
    gamma=2.7
  }
  if(is.null(gamma)){
    gamma=0
  }
  pentype = switch(penalty, LASSO = 1, MCP = 2, SCAD = 3)
  n=dim(X)[1]
  p=dim(X)[2]
  if (missing(max.num)) 
    max.num=p+1 else max.num=min(max.num,p+1)
  if (missing(lambda.min.ratio)) 
    lambda.min.ratio=ifelse(n<p, 0.01, 1e-04)
  ################ prepare variables
  lambda = NULL
  beta.mat = NULL  ##storing the beta coefficents along the path
  beta = rep(0, p)  ##the current beta estimates excluding the interation terms
  index = NULL
  ################ save the original X for generating interactions
  X0 = X
  ################ standardize design matrix
  X = scale(X0) 
  xm = attr(X, "scaled:center")
  xsd = attr(X, "scaled:scale")
  ############# lambda list
  if (family == "gaussian") {
    max.lam = max(abs((1/n)*(t(X)%*%(y-mean(y)))))
    a0list = matrix(mean(y),n.lambda,q+2)
  } else if (family == "binomial") {
    max.lam = max(abs((1/n)*(t(X)%*%(y-mean(y)))))
    a0list = matrix(log(mean(y)/(1 - mean(y))),n.lambda,q+2)
  } else if (family == "poisson") {
    max.lam = max(abs((1/n)*(t(X)%*%(y-mean(y)))))
    a0list = matrix(log(mean(y)), n.lambda,q+2)
  }  
  
  if(missing(lam.list)) {
    min.lam = max.lam * lambda.min.ratio
    lam.list = exp(seq(from = log(max.lam), to = log(min.lam), length.out = n.lambda))
  } else {
    lam.list = lam.list[lam.list <= max.lam]
    n.lambda = length(lam.list)
  }
  ########initialie
  a0=a0list[1,]
  loglik.list = cri.list = AIC.list = BIC.list = EBIC.list = GIC.list = 
    df.list = df.m.list = df.i.list = vector('numeric', n.lambda)
  ind.list.inter = ind.list.main = ind.list.inter.xlab = beta.list.inter = 
    vector('list', n.lambda)
  ############## main part############################################################
  colnames(X) = paste("X", 1:p, sep = "")
  nonPen = rep(0, p)
  for (k in 1:n.lambda) {
    nonPen = rep(0, p) ### heredity force
    break.ind = FALSE
    lam = lam.list[k]
    index = which(abs(beta[1:p]) > eps)  ###selected main effects from last step
    if (length(index) > 0) {
      ### find the candidate interation effects following strong heredity strong heredity
      aa = outer(index, index, f <- function(x, y) {
        paste("X", pmin(x, y), "X", pmax(x, y), sep = "")
      })
      aa = as.vector(aa)
      #bb1 = unique(as.vector(aa))
      #bb = bb1[!grepl("^X([0-9]+)X\\1$", bb1)]  #remove like X1X1 X2X2
      bb=maintointer(index) 
      loc = match(bb, aa)
      newinter = outercprod(X0[, index], X0[, index])
      newinter = newinter[, loc]
      if (hier == "Weak") {
        ### append strong heredity case to form the weak ones.
        rindex = setdiff(1:p, index)
        if (length(rindex) > 0) {
          ## if there are candidate interactions under weak heredity
          naa = outer(index, rindex, f <- function(x, y) {
            paste("X", pmin(x, y), "X", pmax(x, y), sep = "")
          })
          naa = as.vector(naa)
          nnewinter = outercprod(X0[, rindex], X0[, index])
          # colnames(nnewinter) = naa
          newinter = cbind(newinter, nnewinter)
          bb = c(bb, naa)
        }
      }
      curInter=colnames(X)[-(1:p)]
      candInter=setdiff(bb,curInter)
      curloc=match(candInter, bb)
      if (length(index)+length(curloc)>5e5) 
      {
        k=k-1
        break
      }
      newinter = as.matrix(newinter)
      newinter = newinter[,curloc]
      ncurInter = length(curInter)
      ncandInter = length(candInter)
      # cat('k=',k,'candidate interaction', candInter, '\n', sep=' ')
      if (ncurInter > 0 & hier == "Strong") {
        ## active interaction terms, setting the penalty for the parents to 0
        for (indInter in 1:ncurInter) {
          pair = as.numeric(strsplit(curInter[indInter], "X")[[1]][2:3])
          nonPen[pair[1]] = 1
          nonPen[pair[2]] = 1
        }
      }
      # nonPen[index] = 1 Xinter = NULL
      if (ncandInter > 0 && inter) {
        xnewname = c(colnames(X), candInter)
        tmp = scale(newinter)
        X  = cbind(X,tmp)
        colnames(X) = xnewname
        xim1 = attr(tmp, "scaled:center")
        xisd1 = attr(tmp, "scaled:scale")
        xm = c(xm, xim1)
        xsd = c(xsd, xisd1)
        beta = c(beta,rep(0, ncandInter))  #expand the beta coefficent vector
        # to include the candiate interaction terms.
      }
    }
    pf = c(penalty.factor,rep(inter.penalty.factor,ncol(X) - p))
    nonpenind = which(nonPen != 0)
    pf[nonpenind] = 0
    for (ite in 1:max.iter) {
      if (ite == 1) {
        cd.temp1 = cd.general(X = X, y = y, exposure=exposure, Z=Z, a0 = a0, beta = beta, epsilon = eps, 
                              max.iter = 1, lambda = lam, family = family, bInd = break.ind, 
                              pf = pf, pentype = pentype, gamma = gamma)
        a0 = cd.temp1$a0
        beta = cd.temp1$beta
        ind1 = which(abs(beta) > eps)
      }
      # #CD
      if (ite > 1) {
        cd.temp2 = cd.general(X = X[, ind1], y = y,exposure=exposure, Z=Z, a0 = a0, beta = beta[ind1], 
                              epsilon = eps, max.iter = max.iter, lambda = lam, family = family, 
                              bInd = break.ind, pf = pf[ind1], pentype = pentype, 
                              gamma = gamma)
        a0 = cd.temp2$a0
        beta2 = beta
        beta2[ind1] = cd.temp2$beta
        # ########redetect active set check.beta=new.beta
        cd.temp3 = cd.general(X = X, y = y, exposure=exposure, Z=Z, a0 = a0, beta = beta2, epsilon = eps, 
                              max.iter = 1, lambda = lam, family = family, bInd = break.ind, 
                              pf = pf, pentype = pentype, gamma = gamma)
        a0 = cd.temp3$a0
        beta = cd.temp3$beta
        ind3 = which(abs(beta) > eps)
        if (setequal(ind1, ind3)) {
          break
        }
        ind1 = ind3
        
      }  ##END iter>1
    }  ##END iter
    
    ind.list.main[[k]] = which(abs(beta[1:p]) > eps)
    ind.list.inter[[k]] = which(abs(beta[-(1:p)]) > eps)  #record the interaction
    # index pair location list
    size.main = length(ind.list.main[[k]])
    size.inter = length(ind.list.inter[[k]])
    index = which(abs(beta) > eps)
    beta[-index] = 0
    
    if (size.inter > 0 & hier == "Strong") {
      ### if interaction effects are detected, enforce the strong heredity in this step
      tmpindname = colnames(X)[ind.list.inter[[k]] + p]
      cur.main.ind = intertomain(tmpindname)
      if (trace == T) 
        cat("k=", k, "Enforced main effects", setdiff(cur.main.ind, ind.list.main[[k]]), 
            "\n")
      
      ind.list.main[[k]] = union(ind.list.main[[k]], cur.main.ind)
      index = union(index, cur.main.ind)
    }
    size.main = length(ind.list.main[[k]])
    index = sort(index)
    beta.n = beta
    a0.n = a0
    if (refit == TRUE & length(index) > 0 ) {
      lmfit = glm(y ~ cbind(exposure,Z,X[,index]), family = family)
      beta.lmfit = coef(lmfit)
      a0.n = beta.lmfit[1:(q+2)]
      beta.n[index] = beta.lmfit[-(1:(q+2))]
    }
    df.list[k] = size.main + size.inter
    loglik.list[k] = loglik(cbind(1,exposure,Z,X), y, c(a0.n,beta.n), family)
    
    if (length(beta) > p) {
      tmp = which(abs(beta[-(1:p)]) > eps)
      beta = beta[c(1:p, p + tmp)] 
      beta.n = beta.n[c(1:p, p + tmp)]
      X = X[, c(1:p, p + tmp)]
      xm = xm[c(1:p, p + tmp)]
      xsd = xsd[c(1:p, p + tmp)]
      # ind.list.inter.xlab[[k]] = NULL
      if (length(tmp) > 0) {
        ## if interaction effects are selected.
        ind.list.inter.xlab[[k]] = colnames(X)[-(1:p)]
        beta.list.inter[[k]] = beta.n[-(1:p)]/xsd[-(1:p)]
      } 
    }
    if (family == 'binomial' & max(abs(beta)) > 10) {
      k = k-1
      break
    }
    
    beta.s = beta.n/xsd
    a0.s = a0.n - sum(beta.s*xm)
    a0list[k,] = a0.s
    beta.mat = cbind(beta.mat, beta.s[1:p])
    df.m.list[k] = length(ind.list.main[[k]])
    df.i.list[k] = length(beta) - p
    if (df.list[k] >= n - 1) 
      break
    if (break.ind == TRUE) {
      print("Warning: Algorithm failed to converge for all values of lambda")
      break
    }
    if (trace == T) {
      cat("k=", k, "current main effects", ind.list.main[[k]], "\n", sep = " ")
      cat("k=", k, "current interaction", ind.list.inter.xlab[[k]], "\n", sep = " ")
    }
    # end the outer loop: decrease in lambda
  }
  
  if (inter == FALSE) {
    p.eff = p
  } else if (hier == "Strong") {
    p.eff = p + df.m.list *(df.m.list-1)/2
  } else if (hier == "Weak") {
    p.eff = p + df.m.list *(df.m.list-1)/2 + df.m.list*(p-df.m.list)
  }
  
  AIC.list = loglik.list + 2 * df.list
  BIC.list = loglik.list + log(n) * df.list
  EBIC.list = loglik.list + log(n) * df.list + 2 * ebic.gamma * 
    log(choose(p.eff, df.list))
  GIC.list = loglik.list + log(log(n)) * log(p.eff) * df.list
  cri.list = switch(tune, AIC = AIC.list, BIC = BIC.list, EBIC = EBIC.list,
                    GIC = GIC.list)
  region  = which(df.list[1:k] < sqrt(n))
  #browser()
  cri.loc = which.min(cri.list[region])
  AIC.loc = which.min(AIC.list[region])
  BIC.loc = which.min(BIC.list[region])
  EBIC.loc = which.min(EBIC.list[region])
  GIC.loc = which.min(GIC.list[region])
  all.locs = c(AIC.loc, BIC.loc, EBIC.loc, GIC.loc)
  
  lambda = lam.list[1:ncol(beta.mat)]
  # print(cri.loc) browser()
  if (length(ind.list.inter) == 0) {
    interInd = NULL
  } else {
    interInd = ind.list.inter.xlab[[cri.loc]]
  }
  if (length(beta.list.inter) == 0) {
    beta.i = NULL
  } else {
    beta.i = beta.list.inter[[cri.loc]]
  }
  val = list(a0 = a0list[cri.loc,], a0.list = a0list, beta.m.mat = beta.mat, beta.i.mat = beta.list.inter, 
             beta.m = beta.mat[ind.list.main[[cri.loc]], cri.loc], beta.i = beta.i, df = df.list[1:k], 
             df.m = df.m.list[1:k], df.i = df.i.list[1:k], lambda = lambda[1:k], mainInd.list = ind.list.main[1:k], 
             mainInd = ind.list.main[[cri.loc]], cri.list = cri.list[1:k], loglik.list = loglik.list[1:k], 
             cri.loc = cri.loc, all.locs = all.locs, interInd.list = ind.list.inter.xlab[1:k], 
             interInd = interInd, family = family, X = X0, y = y)
  class(val) = "RAMP"
  return(val)
}

print.RAMP = function(x, digits = max(3, getOption("digits") - 3), ...) {
  cat("Important main effects:", colnames(x$X)[x$mainInd], "\n")
  cat("Coefficient estimates for main effects:", signif(x$beta.m, digits), "\n")
  cat("Important interaction effects:", sapply(x$interInd, function(term) {
    idx <- as.numeric(unlist(regmatches(term, gregexpr("[0-9]+", term))))
    paste(colnames(x$X)[idx], collapse = "")
  }), "\n")
  if (length(x$interInd) > 1) {
    cat("Coefficient estimates for interaction effects:", signif(x$beta.i, digits), 
        "\n")
  }
  cat("Exposure estimate:", signif(x$a0[2], digits), "\n")
  cat("Confounder estimate:", signif(x$a0[3:(2+q)], digits), "\n")
}


mainandinter <- function(S, x){
  res <- do.call(cbind, lapply(x, function(t) {
    if (t %in% colnames(S)) {
      return(unname(S[, t]))
    }
    parts <- strcapture("^(M\\d+)(M\\d+)$", t,
                        data.frame(a=character(), b=character()))
    return(unname(S[, parts$a] * S[, parts$b]))
  }))
  colnames(res) <- x
  res
}




### Step 1: Sure Independence Screening (SIS)
HIMA=function(X, M, Y,COV){
 alpha_SIS_est=alpha_SIS_se=alpha_SIS_pvalue=beta_SIS=beta_all=rep(0,p)
  abhat=rep(0,p)
  count_SIS=rep(0,p)
  for (k in 1:p) {
    fit1<-lm(M[,k]~X+COV)
    alpha_SIS_est[k]=summary(fit1)$coefficients[2,1]
    alpha_SIS_pvalue[k]=summary(fit1)$coefficients[2,4]
    alpha_SIS_se[k]=summary(fit1)$coefficients[2,2]
    fit2<-lm(Y~M[,k]+X+COV)
    beta_SIS[k]=summary(fit2)$coefficients[2,1]
    beta_all[k]=summary(fit2)$coefficients[2,4]
  }
  d0=round(n/(log(n)))
  ab_SIS=alpha_SIS_est*beta_SIS
  ID_SIS=which(-abs(ab_SIS) <= sort(-abs(ab_SIS))[d0])
  count_SIS[ID_SIS]=1
  ############Step 2: lasso for selecting beta#######################
  fit <- RAMP(X=M[,ID_SIS],y=Y,exposure=X,Z=COV,penalty='SCAD',hier='Strong')
  main_names=colnames(M[,ID_SIS])[fit$mainInd]
  inter_names <- sapply(fit$interInd, function(term) {
    idx <- as.numeric(unlist(regmatches(term, gregexpr("[0-9]+", term))))
    paste(colnames(M[,ID_SIS])[idx], collapse = "")
  })
  d1=length(main_names)
  d2=length(inter_names)
  d=d1+d2
  if(length(main_names)>0){
  ID_lasso=unname(c(main_names,inter_names))
  fit4=lm(Y~X+COV+.,data=data.frame(Y,X,COV,mainandinter(M,ID_lasso)))
  betahat=summary(fit4)$coef[-c(1:(q+2)),1]
  beta_pvalue=summary(fit4)$coef[-c(1:(q+2)),4]
  ################    the multiple-testing  procedure ####
  bind.main <-rbind(pmin(p.adjust(beta_pvalue[1:d1],method = "fdr"),1), pmin(p.adjust(alpha_SIS_pvalue[ID_SIS[fit$mainInd]],method = "fdr"),1))
  final.main <- apply(bind.main, 2, max)
  ID_main=main_names[which(final.main<=0.05)]
  if(length(ID_main)>1){
  inter_names1=combn(colnames(M[,ID_main]), 2, FUN = function(x) paste(x, collapse = ""))
  ID_inter1=intersect(inter_names1,inter_names)
  p_inter=beta_pvalue[(d1+1):(d1+d2)]
  final.inter=p.adjust(p_inter[match(ID_inter1,names(p_inter))],method = "fdr")
  ID_inter=ID_inter1[which(final.inter<=0.05)]
  d4=length(ID_inter)
  ID_fdr=c(ID_main,ID_inter)
  final.p=c(final.main,final.inter)
  }else{
    ID_fdr=ID_main
    final.p=final.main
  }
  if(length(ID_fdr)>0){
    fit5=lm(Y~X+COV+.,data=data.frame(Y,X,COV,mainandinter(M,ID_fdr)))
    beta_hat=summary(fit5)$coef[-c(1:(q+2)),1]
    beta_se=summary(fit5)$coef[-c(1:(q+2)),2]
    alpha_SIS_est=matrix(alpha_SIS_est,nrow = 1,ncol=p)
    colnames(alpha_SIS_est)=paste0("M",1:p)
    alpha_hat=as.numeric(mainandinter(alpha_SIS_est,ID_fdr))
    alpha_SIS_se=matrix(alpha_SIS_se,nrow = 1,ncol=p)
    colnames(alpha_SIS_se)=paste0("M",1:p)
    alpha_se=as.numeric(mainandinter(alpha_SIS_se,ID_fdr))
    pvalue=final.p[which(final.p<=0.05)]
    IDE=as.numeric(alpha_hat*beta_hat)
    out_result <-data.frame(
      Index = ID_fdr,
      alpha_hat=alpha_hat,
      alpha_se=alpha_se,
      beta_hat=beta_hat,
      beta_se=beta_se,
      IDE=IDE,
      rimp = abs(IDE)/sum(abs(IDE)) * 100,
      pmax = pvalue, row.names = NULL
     )
    }else{
    out_result <- NULL
  }
  }else{
    out_result<- NULL
  }
  return(out_result)
}


library(MASS)
library(mvtnorm)
library(MASS)
library(abind)
library(pracma)
library(qs)##qread
library(haven)
library(dplyr)
library(data.table)
library(readr)
options(max.print=20000)
Y_impute=read.csv("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/Y_impute.csv",check.names = FALSE)
link=read.csv("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/CARDIA_linkTable.csv",check.names = FALSE)
code1<- colnames(Y_impute)[!is.na(match(colnames(Y_impute),link$BARCODE))]
Y_impute=Y_impute[,code1]
link15=link[link$Visit=="Y15",]
Y15=Y_impute[,intersect(colnames(Y_impute),link15$BARCODE)]
link20=link[link$Visit=="Y20",]
Y20=Y_impute[,intersect(colnames(Y_impute),link20$BARCODE)]
link25=link[link$Visit=="Y25",]
Y25=Y_impute[,intersect(colnames(Y_impute),link25$BARCODE)]
link30=link[link$Visit=="Y30",]
Y30=Y_impute[,intersect(colnames(Y_impute),link30$BARCODE)]
colnames(Y15)=link$CARDIA_long[match(colnames(Y15),link$BARCODE)]
colnames(Y20)=link$CARDIA_long[match(colnames(Y20),link$BARCODE)]
colnames(Y25)=link$CARDIA_long[match(colnames(Y25),link$BARCODE)]
colnames(Y30)=link$CARDIA_long[match(colnames(Y30),link$BARCODE)]
M15=t(Y15)
M20=t(Y20)
M25=t(Y25)
M30=t(Y30)
PC=read.csv("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/PC.csv",check.names = FALSE)
cell=read.csv("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/cellProp.csv",check.names = FALSE)
PC15=PC[match(link15$BARCODE,PC$BARCODE),]
PC15$CARDIA_long=link$CARDIA_long[match(PC15$BARCODE,link$BARCODE)]
PC20=PC[match(link20$BARCODE,PC$BARCODE),]
PC20$CARDIA_long=link$CARDIA_long[match(PC20$BARCODE,link$BARCODE)]
PC25=PC[match(link25$BARCODE,PC$BARCODE),]
PC25$CARDIA_long=link$CARDIA_long[match(PC25$BARCODE,link$BARCODE)]
PC30=PC[match(link30$BARCODE,PC$BARCODE),]
PC30$CARDIA_long=link$CARDIA_long[match(PC30$BARCODE,link$BARCODE)]
cell15=cell[match(link15$BARCODE,cell$BARCODE),]
cell15$CARDIA_long=link$CARDIA_long[match(cell15$BARCODE,link$BARCODE)]
cell20=cell[match(link20$BARCODE,cell$BARCODE),]
cell20$CARDIA_long=link$CARDIA_long[match(cell20$BARCODE,link$BARCODE)]
cell25=cell[match(link25$BARCODE,cell$BARCODE),]
cell25$CARDIA_long=link$CARDIA_long[match(cell25$BARCODE,link$BARCODE)]
cell30=cell[match(link30$BARCODE,cell$BARCODE),]
cell30$CARDIA_long=link$CARDIA_long[match(cell30$BARCODE,link$BARCODE)]
Data=read_sas("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/y0_10_covariate.sas7bdat")
cvd=read_sas("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/cac_2025.sas7bdat")
cac=data.frame(ID=cvd$ID,Y25cac=cvd$Y25cactot,Y20cac=cvd$Y20cactot)
cac=cac%>%filter(!is.na(Y20cac))
nsdh_indexs=read_sas("C:/Users/lili/OneDrive - Washington University in St. Louis/Desktop/agedata/nsdh_1210.sas7bdat")
######################################using the mean of Y0,Y10##################
nsdh_indexs=nsdh_indexs %>%filter( !is.na(nSDH_index0))%>%filter( !is.na(nSDH_index10))%>%filter( !is.na(nSDH_index15))
id=intersect(intersect(cac$ID,intersect(nsdh_indexs$ID,Data$ID)),Reduce(union,list(rownames(M15), rownames(M20), rownames(M25), rownames(M30))))
n=length(id)
data=Data%>%filter(ID %in% id)
Z1=data.frame(ID=data$ID,center=data$center_y0,age=data$age_y0,race=data$race_y0,sex=data$sex_y0)
Z2=data.frame(ID=data$ID,center=data$center_y10,age=data$age_y10,race=data$race_y10,sex=data$sex_y10)
Z3=data.frame(ID=data$ID,center=data$center_y0,age=data$age_y0+15,race=data$race_y0,sex=data$sex_y0)
combined_data <- rbind(Z1, Z2,Z3)
Z<- aggregate(. ~ ID, data=combined_data, FUN=mean, na.rm=TRUE)
index=nsdh_indexs%>%filter(ID %in% id)
X15=index$nSDH_index15
X0=index$nSDH_index0
X10=index$nSDH_index10
X <- rep(NA, n)
yearpoint<- c(0,10,15)
for(i in 1:n){
  v <- as.numeric(cbind(X0,X10,X15)[i,])
  if(sum(!is.na(v))>=2 & !is.na(v[1]) & !is.na(v[3]))
  {
    ind = which(!is.na(v))
    cum = 0
    for(j in 1:(length(ind)-1))
    {
      cum = cum + mean(c(v[ind[j]], v[ind[j+1]])) * diff(yearpoint[ind[c(j, j+1)]])
    }
    X[i] <- cum
  }
}

CAC=cac%>%filter(ID %in% id)
ids_in_M15 <- id %in% rownames(M15)
ids_in_M20 <- id%in%rownames(M20)
N <- sum(ids_in_M15)
Zt <- data.frame(matrix(0,nrow = N, ncol = ncol(Z))) 
colnames(Zt) <- colnames(Z)
Mt <- matrix(0,nrow = N, ncol = ncol(M15)) 
PCt<- matrix(0,nrow = N, ncol = 7) 
cellt<- matrix(0,nrow = N, ncol = 6) 
Xt <- rep(0,N)
id1 <- rep(0,N)
cac20<- rep(0,N)
cac25<- rep(0,N)
j <- 1
for(i in 1:n){
  if(id[i]%in%rownames(M15)){
    id1[j] <- i
    Xt[j] <- X[i]
    Zt[j, ] <- Z[i, ]
    Mt[j, ] <- M15[id[i], ]
    PCt[j,]<- as.numeric(PC15[which(PC15$CARDIA_long==id[i]), 1:7])
    cellt[j,]<- as.numeric(cell15[which(cell15$CARDIA_long==id[i]),1:6])
    cac20[j]<-CAC[which(CAC$ID==id[i]),"Y20cac"]
    cac25[j]<-CAC[which(CAC$ID==id[i]),"Y25cac"]
    j <- j + 1
  }
}
######################## M20 ######################################
N <- sum(ids_in_M20)
Zt <- data.frame(matrix(0,nrow = N, ncol = ncol(Z))) 
colnames(Zt) <- colnames(Z)
Mt <- matrix(0,nrow = N, ncol = ncol(M15)) 
PCt<- matrix(0,nrow = N, ncol = 7) 
cellt<- matrix(0,nrow = N, ncol = 6) 
Xt <- rep(0,N)
id1 <- rep(0,N)
cac20<- rep(0,N)
cac25<- rep(0,N)
j <- 1
for(i in 1:n){
  if(id[i]%in%rownames(M20)){
    id1[j] <- i
    Xt[j] <- X[i]
    Zt[j, ] <- Z[i, ]
    Mt[j, ] <- M20[id[i], ]
    PCt[j,]<- as.numeric(PC20[which(PC20$CARDIA_long==id[i]), 1:7])
    cellt[j,]<- as.numeric(cell20[which(cell20$CARDIA_long==id[i]),1:6])
    cac20[j]<-CAC[which(CAC$ID==id[i]),"Y20cac"]
    cac25[j]<-CAC[which(CAC$ID==id[i]),"Y25cac"]
    j <- j + 1
  }
}
################################################################################
colnames(PCt)=colnames(PC15)[1:7]
colnames(cellt)=colnames(cell15)[1:6]
PCt=apply(PCt,2,scale)
cellt=apply(cellt,2,scale)
cellt=cellt[,-1]##remove CD8T
Mt=apply(as.matrix(Mt), 2, as.numeric)
exposure=scale(Xt)
race=ifelse(Zt$race==5,1,0)
center1=ifelse(Zt$center==1,1,0)
center2=ifelse(Zt$center==2,1,0)
center3=ifelse(Zt$center==3,1,0)
sex=ifelse(Zt$sex==1,1,0)
age=scale(Zt$age)
Mt=scale(Mt)
agedata=data.frame(id1=id1,cac20,cac25,exposure,center1,center2,center3,race,sex,age,PCt,cellt)
N=dim(agedata)[1]
p=dim(Mt)[2]
q=18
any(is.na(agedata))
fit=lm(as.formula(paste("cac20~", paste(names(agedata[,-c(1:3)])[1:7], collapse = "+"))),data=agedata)
summary(fit)
Mediator <- data.frame(Mt)
colnames(Mediator) <- paste0("M", 1:ncol(Mt))
HIMA(X=exposure,M=Mediator,Y=cac20,
     COV=cbind(center1,center2,center3,race,sex,age,PCt,cellt))





























