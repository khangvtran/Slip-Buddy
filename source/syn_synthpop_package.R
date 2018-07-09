### Author: Beata Nowok, Gillian M Raab, Chris Dibben
### University of Edinburgh 
### synthpop: Bespoke Creation of Synthetic Data in R


function (data, method = vector("character", length = ncol(data)), 
    visit.sequence = (1:ncol(data)), predictor.matrix = NULL, 
    m = 1, k = nrow(data), proper = FALSE, minnumlevels = -1, 
    maxfaclevels = 60, rules = NULL, rvalues = NULL, cont.na = NULL, 
    semicont = NULL, smoothing = NULL, event = NULL, denom = NULL, 
    drop.not.used = FALSE, drop.pred.only = FALSE, default.method = c("normrank", 
        "logreg", "polyreg", "polr"), models = FALSE, print.flag = TRUE, 
    seed = "sample", ...) 
{
    obs.vars <- names(data)
    if (all(method == "")) 
        method = "cart"
    if (!is.null(attr(data, "filetype")) && attr(data, "filetype") == 
        "sav") {
        var.lab <- attr(data, "variable.labels")
        val.lab <- attr(data, "label.table")
    }
    else {
        var.lab <- val.lab <- NULL
    }
    if (is.character(visit.sequence)) {
        nametoind <- match(visit.sequence, colnames(data))
        if (any(is.na(nametoind))) 
            stop("Unrecognized variable(s) in visit.sequence: ", 
                paste(visit.sequence[is.na(nametoind)], collapse = ", "), 
                call. = FALSE)
        else visit.sequence <- nametoind
    }
    check.visit.sequence.syn <- function(setup) {
        vis <- setup$visit.sequence
        nvar <- setup$nvar
        varnames <- setup$varnames
        method <- setup$method
        if (any(duplicated(vis))) 
            stop("Visit sequence includes repeated variable names/numbers.\n", 
                call. = FALSE)
        if (any(!(vis %in% 1:nvar))) {
            cat("Element(s): {", paste(vis[!(vis %in% 1:nvar)], 
                collapse = ", "), "} of the 'visit.sequence' removed as not valid. No such column.\n\n", 
                sep = "")
            vis <- as.numeric(vis[vis %in% 1:nvar])
        }
        event.in.vis <- !is.na(match(vis, event))
        if (!is.null(event) & any(event.in.vis)) {
            cat("Element(s) {", paste(vis[event.in.vis], collapse = ", "), 
                "} of the 'visit.sequence' with method(s) {", 
                paste(method[vis[event.in.vis]], collapse = ", "), 
                "} removed because used as event indicator(s).\nAny event indicators will be synthesised along with the corresponding survival time(s). \n\n")
            vis <- vis[!event.in.vis]
            if (length(vis) < 2) 
                stop("Visit sequence now of length ", length(vis), 
                  ". No synthesis done.")
        }
        for (j in which(denom[vis] > 0)) {
            denom.pos <- match(denom[vis][j], vis)
            if (j < denom.pos) 
                stop("Denominator ", varnames[denom[vis][j]], 
                  " for ", varnames[vis[j]], " must be synthesisied before it\n", 
                  call. = FALSE)
        }
        if (length(vis) == 0) 
            stop(paste("Seems no variables being synthesised.\nCheck parameter 'visit.sequence'."))
        for (j in which(is.passive(method[vis]))) {
            var.present <- match(all.vars(as.formula(method[vis][j])), 
                varnames)
            var.in.vis <- match(var.present, vis)
            if (j < max(var.in.vis) | any(is.na(var.in.vis))) 
                stop("Variable(s) used in passive synthesis for ", 
                  varnames[vis][j], " has/have to be synthesised BEFORE the variables they apply to.")
        }
        setup$visit.sequence <- vis
        return(setup)
    }
    check.predictor.matrix.syn <- function(setup) {
        pred <- setup$predictor.matrix
        nvar <- setup$nvar
        varnames <- setup$varnames
        vis <- setup$visit.sequence
        method <- setup$method
        denom <- setup$denom
        pred.dt <- matrix(0, nvar, nvar)
        pred.dt[vis, vis] <- outer(1:length(vis), 1:length(vis), 
            ">")
        if (is.null(pred)) 
            pred <- pred.dt
        dimnames(pred) <- list(varnames, varnames)
        diag(pred) <- 0
        vis.syn <- vis
        if (!all(method == "") & length(method) > 1) 
            vis.syn <- intersect(vis, which(method != ""))
        if (length(vis.syn) < length(vis)) {
            vis.blank <- setdiff(vis, vis.syn)
            pred[vis.blank, ] <- 0
        }
        pred[setdiff(1:nvar, vis), ] <- 0
        for (j in which(method == "sample")) pred[j, ] <- 0
        for (j in which(method == "survctree")) pred[, j] <- 0
        for (j in which(method == "survctree" & event > 0)) pred[, 
            event[j]] <- 0
        for (j in which(method == "logreg")) {
            if (denom[j] > 0) 
                pred[j, denom[j]] <- 0
        }
        preddel <- which((pred[, vis.syn, drop = FALSE] == 1 & 
            pred.dt[, vis.syn, drop = FALSE] == 0), arr.ind = TRUE)
        if (length(vis) > 1) {
            pred[, vis.syn] <- ifelse((pred[, vis.syn] == 1 & 
                pred.dt[, vis.syn] == 0), 0, pred[, vis.syn])
            if (nrow(preddel) > 0) 
                cat(paste("Not synthesised predictor ", varnames[vis.syn][preddel[, 
                  2]], " removed from predictor.matrix for variable ", 
                  varnames[preddel[, 1]], ".\n", sep = ""))
        }
        setup$predictor.matrix <- pred
        setup$visit.sequence <- vis
        return(setup)
    }
    check.method.syn <- function(setup, data, proper) {
        method <- setup$method
        default.method <- setup$default.method
        vis <- setup$visit.sequence
        nvar <- setup$nvar
        varnames <- setup$varnames
        pred <- setup$predictor.matrix
        event <- setup$event
        denom <- setup$denom
        if (sum(pred) > 0) 
            has.pred <- apply(pred != 0, 1, any)
        else has.pred <- rep(0, nvar)
        for (j in 1:nvar) {
            if (!is.passive(method[j])) {
                if (is.numeric(data[, j])) {
                  v <- var(data[, j], na.rm = TRUE)
                  if (!is.na(v)) 
                    constant <- (v < 1000 * .Machine$double.eps)
                  else constant <- is.na(v) | v < 1000 * .Machine$double.eps
                }
                else {
                  constant <- all(duplicated(data[, j])[-1L])
                }
                if (constant) {
                  if (any(vis == j)) {
                    method[j] <- "constant"
                    if (print.flag == T) 
                      cat("\nVariable ", varnames[j], " has only one value so its method has been changed to \"constant\".\n", 
                        sep = "")
                    pred[j, ] <- 0
                  }
                  if (any(pred[, j] != 0)) {
                    if (print.flag == T) 
                      cat("Variable ", varnames[j], " removed as predictor because only one value.\n", 
                        sep = "")
                    pred[, j] <- 0
                  }
                }
            }
        }
        nestmth.idx <- grep("nested", method)
        gr.vars <- vector("character", length(method))
        gr.vars[nestmth.idx] <- substring(method[nestmth.idx], 
            8)
        if (length(nestmth.idx) > 0) {
            for (i in nestmth.idx) {
                if (gr.vars[i] == "") 
                  stop("No variable name provided for 'nested' method for ", 
                    varnames[i], ".\nSet method as 'nested.varname' instead of 'nested'.\n", 
                    call. = FALSE)
                if (!(gr.vars[i] %in% varnames)) 
                  stop("Unrecognized variable ", gr.vars[i], 
                    " provided for 'nested' method for ", varnames[i], 
                    "\n", call. = FALSE)
                if (gr.vars[i] == varnames[i]) 
                  stop("Variable ", varnames[i], " can not be predicted by itself.\n", 
                    call. = FALSE)
                tabvars <- table(data[, i], data[, gr.vars[i]])
                tabvars01 <- ifelse(tabvars > 0, 1, 0)
                ymulti <- rowSums(tabvars01) > 1
                if ("NAtemp" %in% names(ymulti)) 
                  ymulti["NAtemp"] <- FALSE
                if (any(ymulti)) 
                  cat("\nNOTE: Variable", varnames[i], "is not nested within its predictor", 
                    gr.vars[i], ". Check categories:", paste0(rownames(tabvars01)[ymulti], 
                      collapse = ", "), "\n", sep = " ")
                pred[i, -match(gr.vars[i], varnames)] <- 0
                pred[-match(varnames[i], gr.vars), i] <- 0
            }
            if (m > 0) 
                method[nestmth.idx] <- "nested"
        }
        if (any(method == "parametric")) {
            if (length(vis) > 1) {
                for (j in vis[-1]) {
                  if (has.pred[j]) {
                    y <- data[, j]
                    if (is.numeric(y)) 
                      method[j] <- default.method[1]
                    else if (nlevels(y) == 2) 
                      method[j] <- default.method[2]
                    else if (is.ordered(y) & nlevels(y) > 2) 
                      method[j] <- default.method[4]
                    else if (nlevels(y) > 2) 
                      method[j] <- default.method[3]
                    else if (is.logical(y)) 
                      method[j] <- default.method[2]
                    else if (nlevels(y) != 1) 
                      stop("Variable ", j, " ", varnames[j], 
                        " type not numeric or factor.")
                  }
                }
            }
        }
        active <- !is.passive(method) & !(method == "") & !(method == 
            "constant")
        if (sum(active) > 0) {
            fullNames <- method[active]
            if (m == 0) 
                fullNames[grep("nested", fullNames)] <- "nested"
            fullNames <- paste("syn", fullNames, sep = ".")
            notFound <- !sapply(fullNames, exists, mode = "function", 
                inherit = TRUE)
            if (any(notFound)) 
                stop(paste("The following functions were not found:", 
                  paste(fullNames[notFound], collapse = ", ")))
        }
        for (j in vis) {
            y <- data[, j]
            vname <- colnames(data)[j]
            mj <- method[j]
            mlist <- list(m1 = c("logreg", "polyreg", "polr"), 
                m2 = c("norm", "normrank", "survctree"), m3 = c("norm", 
                  "normrank", "survctree", "logreg"))
            if (denom[j] > 0) {
                if (!(mj %in% c("logreg"))) {
                  method[j] <- "logreg"
                  cat("Variable ", vname, " has denominator (", 
                    colnames(data[denom[j]]), ") and method ", 
                    mj, " has been changed to logreg\n", sep = "")
                }
                if (!((is.integer(y) | all((y - round(y)) == 
                  0, na.rm = TRUE)) & (is.integer(data[denom[j]]) | 
                  all((data[denom[j]] - round(data[denom[j]]) == 
                    0), na.rm = TRUE)))) 
                  stop("Variable ", vname, " and denominator ", 
                    colnames(data[denom[j]]), " must be integers\n", 
                    call. = FALSE)
                if (any((data[denom[j]] - y) < 0, na.rm = TRUE)) 
                  stop("Variable ", vname, " must be less than or equal denominator ", 
                    colnames(data[denom[j]]), "\n", call. = FALSE)
            }
            else {
                if (is.numeric(y) & (mj %in% mlist$m1)) {
                  stop("Type mismatch for variable ", vname, 
                    ".\nSyhthesis method \"", mj, "\" is for categorical data.", 
                    sep = "", call. = FALSE)
                }
                else if (is.factor(y) & nlevels(y) == 2 & (mj %in% 
                  mlist$m2)) {
                  stop("Type mismatch for variable ", vname, 
                    ".\nSyhthesis method \"", mj, "\" is not for factors.", 
                    sep = "", call. = FALSE)
                }
                else if (is.factor(y) & nlevels(y) > 2 & (mj %in% 
                  mlist$m3)) {
                  stop("Type mismatch for variable ", vname, 
                    ".\nSyhthesis method \"", mj, "\" is not for factors with three or more levels.", 
                    sep = "", call. = FALSE)
                }
            }
        }
        if (sum(pred) > 0) 
            has.pred <- apply(pred != 0, 1, any)
        else has.pred <- rep(0, sqrt(length(pred)))
        for (j in vis) {
            if (!has.pred[j] & substr(method[j], 1, 6) != "nested" & 
                is.na(any(match(method[j], c("", "constant", 
                  "sample", "sample.proper", "norm", "norm.proper", 
                  "logreg", "logreg.proper"))))) {
                if (print.flag == TRUE) 
                  cat("\nMethod \"", method[j], "\" is not valid for a variable without predictors (", 
                    names(data)[j], ")\nMethod has been changed to \"sample\"\n\n", 
                    sep = "")
                method[j] <- "sample"
            }
        }
        if (any(method == "survctree")) {
            for (j in vis) {
                y <- data[, j]
                vname <- colnames(data)[j]
                mj <- method[j]
                if (mj == "survctree") {
                  if (!is.numeric(y)) 
                    stop("Variable ", vname, " should be a numeric survival time.")
                  if (any(!is.na(y) & y < 0)) 
                    stop("Variable ", vname, " should be a non-negative survival time.")
                  if (is.na((match(event[j], 1:nvar)))) {
                    cat("Variable ", vname, " is a survival time. Corresponding event not in data, assuming no censoring.\n\n", 
                      sep = "")
                    event[j] <- -1
                  }
                  else {
                    tabEI <- table(data[, event[j]])
                    if (length(tabEI) != 2) {
                      if (length(tabEI) == 1 & all(tabEI == 1)) 
                        cat("Variable ", vname, " is a survival time with all cases having events.\n", 
                          sep = "")
                      else if (length(tabEI) == 1 & all(tabEI == 
                        0)) 
                        stop("Variable ", vname, " is a survival time with no cases having events.\n", 
                          "Estimation not possible.", sep = "")
                      else stop("Event must be binary 0/1 but has values {", 
                        paste(names(tabEI), collapse = ", "), 
                        "}.\nNo data synthesised.")
                    }
                    if (!all(as.character(names(tabEI)) == c("0", 
                      "1")) && !is.logical(data[, event[j]])) {
                      stop("Event must be binary 0/1 but it is a ", 
                        class(data[, event[j]]), " variable with values {", 
                        paste(names(tabEI)[1:2], collapse = ", "), 
                        "}.", sep = "")
                    }
                  }
                }
                else {
                  if (event[j] != 0) {
                    cat("Event for variable ", vname, " set to ", 
                      event[j], " although method is \"", mj, 
                      "\". Event reset to 0.\n", sep = "")
                    event[j] <- 0
                  }
                }
            }
        }
        else if (!all(event == 0)) {
            cat("No variables have a survival method so event vector which was \n{", 
                paste(event, collapse = ","), "} set to 0s.\n\n", 
                sep = "")
            event <- rep(0, nvar)
        }
        if (sum(pred > 0) & m > 0) {
            inpred <- apply(pred != 0, 1, any) | apply(pred != 
                0, 2, any)
            if (any(inpred)) {
                collout <- collinear.out(data[, inpred, drop = FALSE])
                if (length(collout) > 0) {
                  for (i in 1:length(collout)) {
                    if (print.flag) 
                      cat("\nVariables ", paste(collout[[i]], 
                        collapse = ", "), " are collinear.\n", 
                        sep = "")
                    vars <- match(collout[[i]], varnames[vis])
                    vfirst <- collout[[i]][vars == min(vars)]
                    nfirst <- match(vfirst, varnames)
                    nall <- match(collout[[i]], varnames)
                    if (print.flag) 
                      cat("\nVariables later in visit.sequence are derived from ", 
                        vfirst, ".\n", sep = "")
                    for (ii in nall) {
                      if (ii != nfirst) {
                        method[ii] <- "collinear"
                        pred[ii, ] <- 0
                        pred[, ii] <- 0
                        pred[ii, nfirst] <- 1
                      }
                    }
                  }
                }
            }
        }
        setup$event <- event
        setup$method <- method
        setup$predictor.matrix <- pred
        setup$visit.sequence <- vis
        setup$denom <- denom
        return(setup)
    }
    check.rules.syn <- function(setup, data) {
        rules <- setup$rules
        rvalues <- setup$rvalues
        pred <- setup$predictor.matrix
        nvar <- setup$nvar
        varnames <- setup$varnames
        method <- setup$method
        vis <- setup$visit.sequence
        if (any(sapply(rules, length) != sapply(rvalues, length))) 
            stop("The number of data rules for each variable should equal the number of corresponding values.\n  Check variable(s): ", 
                paste(varnames[sapply(rules, length) != sapply(rvalues, 
                  length)], collapse = ", "), ".")
        char.allowed <- c("", "|", "||", "&", "&&", "==", ">=", 
            "<=", "<", ">", "!=", "==-", ">=-", "<=-", "<-", 
            ">-", "!=-", "=='", ".", ")", "(", ";", "-", "'", 
            "\"", "\"(", ")\"", "'(", ")'")
        char.present <- paste(gsub("\\w", " ", unlist(rules)), 
            collapse = " ")
        char.present <- strsplit(char.present, "[[:space:]]+")[[1]]
        char.wrong <- !(char.present %in% char.allowed)
        rule.sep <- lapply(sapply(rules, strsplit, "[|&]"), unlist)
        get.vars <- lapply(rule.sep, function(x) gsub("[<>=!].*", 
            "", x))
        get.vars <- lapply(get.vars, function(x) gsub(" ", "", 
            x))
        get.vars <- lapply(get.vars, function(x) gsub("[\\(\\)]", 
            "", x))
        get.vars <- lapply(get.vars, function(x) gsub("is.na", 
            "", x))
        get.vars <- lapply(get.vars, function(x) x[x != ""])
        vars.in.rules <- unique(unlist(get.vars))
        vars.wrong <- !(vars.in.rules %in% varnames)
        if (any(vars.wrong)) 
            stop("Unexpected variable(s) in rules: ", paste(vars.in.rules[vars.wrong], 
                collapse = ", "), ".", call. = FALSE)
        if (any(char.wrong)) {
            cat("One of rules may not be correct. If this is the case compare your rules and Error below.\nOtherwise rules have been applied.\n")
            rs <- unlist(rules)
            names(rs) <- varnames
            rs <- cbind(rs[rs != ""])
            colnames(rs) <- ""
            cat("\nYour rules are:")
            print(rs)
            cat("\n")
        }
        nonmissing <- vector("list", nvar)
        isfactor <- sapply(data, is.factor)
        yes.rules <- sapply(rules, function(x) any(x != ""))
        lth.rules <- sapply(rules, length)
        for (i in 1:nvar) {
            if (yes.rules[i]) {
                for (r in 1:lth.rules[i]) {
                  if (is.na(rvalues[[i]][r]) & !isfactor[i]) {
                    nonmissing[[i]][r] <- with(data, sum(!is.na(data[eval(parse(text = rules[[i]][r])), 
                      i])))
                  }
                  else if (is.na(rvalues[[i]][r]) & isfactor[i]) {
                    nonmissing[[i]][r] <- with(data, sum(as.character(data[eval(parse(text = rules[[i]][r])), 
                      i]) != "NAtemp" & as.character(data[eval(parse(text = rules[[i]][r])), 
                      i]) != "NAlogical"))
                  }
                  else {
                    nonmissing[[i]][r] <- with(data, sum(data[eval(parse(text = rules[[i]][r])), 
                      i] != rvalues[[i]][r] | is.na(data[eval(parse(text = rules[[i]][r])), 
                      i])))
                  }
                }
            }
        }
        any.nonmissing <- sapply(nonmissing, function(x) any(x > 
            0))
        if (any(any.nonmissing) > 0) 
            cat("\nUnexpected values (not obeying the rules) found for variable(s): ", 
                paste(varnames[any.nonmissing > 0], collapse = ", "), 
                ".\nRules have been applied but make sure they are correct.\n", 
                sep = "")
        var.position <- lapply(get.vars, function(x) match(unique(x), 
            varnames))
        var.in.vis <- lapply(var.position, function(x) if (length(x) == 
            0) {
            x <- 0
        }
        else if (any(is.na(match(x, vis)))) {
            x[!is.na(match(x, vis))] <- match(x, vis)
            x[is.na(match(x, vis))] <- nvar
        }
        else {
            x <- match(x, vis)
        })
        max.seq <- sapply(var.in.vis, max, na.rm = T)
        not.synth <- match(1:nvar, vis)[!is.na(match(1:nvar, 
            vis))] <= max.seq[!is.na(match(1:nvar, vis))]
        if (any(not.synth, na.rm = TRUE)) 
            stop("Variable(s) used in missing data rules for ", 
                paste(varnames[!is.na(match(1:nvar, vis))][not.synth & 
                  !is.na(not.synth)], collapse = " "), " have to be synthesised BEFORE the variables they apply to.")
        patternRules <- matrix(0, nrow = nrow(data), ncol = ncol(data))
        for (i in 1:nvar) {
            if (yes.rules[i]) {
                for (r in 1:lth.rules[i]) {
                  if (is.na(rvalues[[i]][r])) 
                    patternRules[with(data, eval(parse(text = rules[[i]][r]))), 
                      i] <- 1
                }
            }
        }
        patternNA <- is.na(data) + 0
        patternNA <- ifelse(patternRules == patternNA, patternNA, 
            0)
        diffNAij <- function(i, j, dataNA) sum(dataNA[, i] - 
            dataNA[, j] < 0)
        diffNA <- Vectorize(diffNAij, vectorize.args = list("i", 
            "j"))
        predNA <- outer(1:nvar, 1:nvar, diffNA, dataNA = patternNA)
        setup$predictor.matrix <- pred
        return(setup)
    }
    namedlist <- function(x, varnames = colnames(data), nvars = length(varnames), 
        missval = NA, argname, argdescription = "", asvector = FALSE) {
        if (is.null(x)) {
            x <- as.list(rep(missval, nvars))
        }
        else if (!is.list(x) | any(names(x) == "") | is.null(names(x))) {
            stop("Argument '", argname, "' must be a named list with names of selected ", 
                argdescription, " variables.", call. = FALSE)
        }
        else {
            x.missval <- as.list(rep(missval, nvars))
            x.ind <- match(names(x), varnames)
            if (any(is.na(x.ind))) 
                stop("Unrecognized variable names in '", argname, 
                  "': ", paste(names(x)[is.na(x.ind)], collapse = ", "), 
                  call. = FALSE)
            if (argname %in% c("denom", "event") & is.character(argname)) {
                denom.ind <- lapply(x, match, varnames)
                if (any(is.na(denom.ind))) 
                  stop("Unrecognized variable(s) provided as ", 
                    argname, "(s): ", paste(unlist(x)[is.na(denom.ind)], 
                      collapse = ", "), call. = FALSE)
                x <- denom.ind
            }
            x.missval[x.ind] <- x
            x <- x.missval
        }
        if (asvector) 
            x <- unlist(x)
        return(x)
    }
    call <- match.call()
    nvar <- ncol(data)
    if (!is.na(seed) & seed == "sample") {
        seed <- sample.int(1000, 1)
    }
    if (!is.na(seed)) 
        set.seed(seed)
    if (!(is.matrix(data) | is.data.frame(data))) 
        stop("Data should be a matrix or data frame.")
    if (nvar < 2) 
        stop("Data should contain at least two columns.")
    if (k != nrow(data) & print.flag == TRUE & m > 0) {
        cat("Sample(s) of size ", k, " will be generated from original data of size ", 
            nrow(data), ".\n\n", sep = "")
    }
    method <- gsub(" ", "", method)
    if (length(method) == 1) {
        if (is.passive(method)) 
            stop("Cannot have a passive syhthesising method for every column.")
        method <- rep(method, nvar)
        method[visit.sequence[1]] <- "sample"
        method[setdiff(1:nvar, visit.sequence)] <- ""
    }
    if (length(method) != nvar) 
        stop(paste("The length of method (", length(method), 
            ") does not match the number of columns in the data (", 
            nvar, ").", sep = ""), call. = FALSE)
    if (!is.null(predictor.matrix)) {
        if (!is.matrix(predictor.matrix)) {
            stop("Argument 'predictor.matrix' is not a matrix.")
        }
        else if (nvar != nrow(predictor.matrix) | nvar != ncol(predictor.matrix)) 
            stop(paste("The 'predictor.matrix' has ", nrow(predictor.matrix), 
                " row(s) and ", ncol(predictor.matrix), " column(s). \nBoth should match the number of columns in the data (", 
                nvar, ").", sep = ""))
    }
    data <- as.data.frame(data)
    varnames <- dimnames(data)[[2]]
    semicont <- namedlist(semicont, missval = NA, argname = "semicont", 
        argdescription = "semi-continuous")
    cont.na <- namedlist(cont.na, missval = NA, argname = "cont.na", 
        argdescription = "")
    cont.na.ini <- cont.na
    cont.na <- mapply(c, cont.na, semicont, SIMPLIFY = FALSE)
    cont.na <- lapply(cont.na, unique)
    rules <- namedlist(rules, missval = "", argname = "rules", 
        argdescription = "")
    rvalues <- namedlist(rvalues, missval = NA, argname = "rvalues", 
        argdescription = "")
    smoothing <- namedlist(smoothing, missval = "", argname = "smoothing", 
        argdescription = "", asvector = TRUE)
    if (any(smoothing != "")) {
        varsmoothind <- which(smoothing != "")
        varnumind <- which(sapply(data, is.numeric))
        smoothnumind <- match(varsmoothind, varnumind)
        if (any(is.na(smoothnumind)) & print.flag == TRUE) 
            cat("\nSmoothing can only be applied to numeric variables.\nNo smoothing will be applied to variable(s): ", 
                paste(varnames[varsmoothind[is.na(smoothnumind)]], 
                  collapse = ", "), "\n", sep = "")
        smoothing[varsmoothind[is.na(smoothnumind)]] <- ""
    }
    denom <- namedlist(denom, missval = 0, argname = "denom", 
        asvector = TRUE)
    event <- namedlist(event, missval = 0, argname = "event", 
        asvector = TRUE)
    setup <- list(visit.sequence = visit.sequence, method = method, 
        default.method = default.method, predictor.matrix = predictor.matrix, 
        nvar = nvar, varnames = varnames, rules = rules, rvalues = rvalues, 
        cont.na = cont.na, event = event, denom = denom)
    setup <- check.visit.sequence.syn(setup)
    setup <- check.predictor.matrix.syn(setup)
    if (!is.null(setup$predictor.matrix) & sum(setup$predictor.matrix > 
        0)) {
        inpred <- apply(setup$predictor.matrix != 0, 1, any) * 
            (!(method %in% c("", "sample"))) | apply(setup$predictor.matrix != 
            0, 2, any)
    }
    else {
        inpred <- rep(FALSE, sqrt(length(setup$predictor.matrix)))
    }
    notevent <- is.na(match(1:nvar, setup$event))
    ischar <- sapply(data, is.character)
    chartofac <- (ischar * inpred) > 0
    if (sum(chartofac) > 0) {
        cat("\nVariable(s):", paste0(varnames[chartofac], collapse = ", "), 
            "have been changed from character to factor.\n", 
            sep = " ")
        for (j in (1:nvar)[chartofac]) data[, j] <- as.factor(data[, 
            j])
    }
    nlevel <- sapply(data, function(x) length(table(x)))
    ifnum <- sapply(data, is.numeric)
    vartofactor <- which(nlevel <= minnumlevels & ifnum & inpred & 
        notevent)
    for (j in vartofactor) data[, j] <- as.factor(data[, j])
    if (length(vartofactor) > 0) {
        cat("\nVariable(s): ", paste0(varnames[vartofactor], 
            collapse = ", "), "numeric but with fewer than", 
            minnumlevels, "levels turned into factor(s).\n\n", 
            sep = " ")
        for (j in vartofactor) {
            if (setup$method[j] %in% c("norm", "norm.proper", 
                "normrank", "normrank.proper")) {
                if (nlevel[j] == 2) 
                  setup$method[j] <- default.method[2]
                else setup$method[j] <- default.method[3]
                cat("Method for ", varnames[j], " changed to ", 
                  setup$method[j], "\n\n")
            }
        }
    }
    isfactor <- sapply(data, is.factor)
    for (j in (1:nvar)[isfactor & inpred & notevent]) {
        data[, j] <- addNA(data[, j], ifany = TRUE)
        levels(data[, j])[is.na(levels(data[, j]))] <- "NAtemp"
    }
    islogicalNA <- sapply(data, function(x) (is.logical(x) & 
        any(is.na(x))))
    for (j in (1:nvar)[islogicalNA & inpred & notevent]) {
        data[, j] <- addNA(data[, j], ifany = TRUE)
        levels(data[, j])[is.na(levels(data[, j]))] <- "NAlogical"
    }
    no.fac.levels <- sapply(data, function(x) length(levels(x)))
    too.many.levels <- no.fac.levels > maxfaclevels
    notsmapling <- !(grepl("nested", method) | grepl("sample", 
        method))
    if (any(inpred & too.many.levels & notsmapling)) {
        stop("Factor(s) with more than ", maxfaclevels, " levels: ", 
            paste0(varnames[inpred & too.many.levels], " (", 
                no.fac.levels[inpred & too.many.levels], ")", 
                collapse = ", "), call. = FALSE, "\nYou can increase 'maxfaclevels' to continue but it may cause computational problems. \nConsider removing factor(s) from prediction matrix, combining categories or using 'nested' method.\n\n")
    }
    setup <- check.method.syn(setup, data, proper)
    if (any(rules != "")) 
        setup <- check.rules.syn(setup, data)
    method <- setup$method
    predictor.matrix <- setup$predictor.matrix
    visit.sequence <- setup$visit.sequence
    event <- setup$event
    rules <- setup$rules
    rvalues <- setup$rvalues
    cont.na <- setup$cont.na
    default.method <- setup$default.method
    denom <- setup$denom
    if (sum(predictor.matrix) > 0) {
        inpred <- apply(predictor.matrix != 0, 1, any) | apply(predictor.matrix != 
            0, 2, any)
        ispredictor <- apply(predictor.matrix != 0, 2, any)
    }
    else inpred <- ispredictor <- rep(0, sqrt(length(predictor.matrix)))
    notinvs <- is.na(match(1:nvar, visit.sequence))
    notsynth <- notinvs | (!notinvs & method == "")
    notevent <- is.na(match(1:nvar, event))
    out <- !inpred & notevent & notsynth
    if (any(out) & print.flag == TRUE) {
        cat("\nVariable(s):", paste0(varnames[out], collapse = ", "), 
            "not synthesised or used in prediction.\n", sep = " ")
        if (drop.not.used == T) 
            cat("The variable(s) will be removed from data and not saved in synthesised data.\n\n")
        else cat("CAUTION: The synthesised data will contain the variable(s) unchanged.\n\n")
    }
    if (any(out) & drop.not.used == T) {
        if (sum(!out) == 0) 
            stop("No variables left to be synthesised")
        newnumbers <- rep(0, nvar)
        newnumbers[!out] <- 1:sum(!out)
        visit.sequence <- newnumbers[visit.sequence]
        visit.sequence <- visit.sequence[!visit.sequence == 0]
        predictor.matrix <- predictor.matrix[!out, !out]
        event[event != 0] <- newnumbers[event[event != 0]]
        event <- event[!out]
        denom[denom != 0] <- newnumbers[denom[denom != 0]]
        denom <- denom[!out]
        data <- data[, !out]
        nvar <- sum(!out)
        method <- method[!out]
        varnames <- varnames[!out]
        if (nvar == 1) {
            cl <- class(data)
            data <- data.frame(data)
            if (cl == "character") 
                data[, 1] <- as.character(data[, 1])
            names(data) <- varnames
        }
        cont.na <- cont.na[!out]
        cont.na.ini <- cont.na.ini[!out]
        semicont <- semicont[!out]
        smoothing <- smoothing[!out]
        rules <- rules[!out]
        rvalues <- rvalues[!out]
        var.lab <- var.lab[!out]
        val.lab <- val.lab[!out]
        if (sum(predictor.matrix > 0)) {
            inpred <- apply(predictor.matrix != 0, 1, any) | 
                apply(predictor.matrix != 0, 2, any)
            ispredictor <- apply(predictor.matrix != 0, 2, any)
        }
        else inpred <- ispredictor <- rep(0, sqrt(length(predictor.matrix)))
        notinvs <- is.na(match(1:nvar, visit.sequence))
        notsynth <- notinvs | (!notinvs & method == "")
        notevent <- is.na(match(1:nvar, event))
    }
    pred.not.syn <- (ispredictor & notsynth)
    if (sum(pred.not.syn) > 0 & drop.pred.only == FALSE) 
        pred.not.syn[pred.not.syn == TRUE] <- FALSE
    if (sum(pred.not.syn) > 0 & print.flag == TRUE) {
        cat("\nVariable(s):", paste0(varnames[ispredictor & notsynth], 
            collapse = ", "), "used as predictors but not synthesised.\n", 
            sep = " ")
        if (drop.pred.only == T) {
            cat("The variable(s) will not be saved with the synthesised data.\n")
        }
        else {
            cat("CAUTION: The synthesised data will contain the variable(s) unchanged.\n")
        }
    }
    if (sum(predictor.matrix) > 0) {
        pm <- padMis.syn(data, method, predictor.matrix, visit.sequence, 
            nvar, rules, rvalues, default.method, cont.na, smoothing, 
            event, denom)
        p <- padModel.syn(pm$data, pm$method, pm$predictor.matrix, 
            pm$visit.sequence, pm$nvar, pm$rules, pm$rvalues, 
            pm$factorNA, pm$smoothing, pm$event, pm$denom)
        if (k != dim(data)[1]) {
            p$syn <- p$syn[sample(1:nrow(data), k, replace = TRUE), 
                ]
            dimnames(p$syn)[[1]] <- 1:k
        }
        if (sum(duplicated(names(p$data))) > 0) 
            stop("Column names of padded data should be unique.")
    }
    else {
        p <- list(data = data, syn = data, predictor.matrix = predictor.matrix, 
            method = method, visit.sequence = visit.sequence, 
            rules = rules, rvalues = rvalues, cont.na = cont.na, 
            event = event, denom = denom, categories = NULL, 
            smoothing = smoothing)
    }
    if (m > 0) {
        syn <- vector("list", m)
        for (i in 1:m) {
            syn[[i]] <- data[0, ]
            syn[[i]] <- syn[[i]][1:k, ]
            dimnames(syn[[i]])[[1]] <- 1:k
        }
    }
    else syn <- NULL
    synall <- sampler.syn(p, data, m, syn, visit.sequence, rules, 
        rvalues, event, proper, print.flag, k, pred.not.syn, 
        models, ...)
    syn <- synall$syn
    fits <- synall$fits
    if (m == 1) {
        syn <- syn[[1]]
        fits <- fits[[1]]
    }
    names(method) <- varnames
    names(visit.sequence) <- varnames[visit.sequence]
    syndsobj <- list(call = call, m = m, syn = syn, method = method, 
        visit.sequence = visit.sequence, predictor.matrix = predictor.matrix, 
        smoothing = smoothing, event = event, denom = denom, 
        proper = proper, n = nrow(data), k = k, rules = rules, 
        rvalues = rvalues, cont.na = cont.na.ini, semicont = semicont, 
        drop.not.used = drop.not.used, drop.pred.only = drop.pred.only, 
        models = fits, seed = seed, var.lab = var.lab, val.lab = val.lab, 
        obs.vars = obs.vars)
    class(syndsobj) <- "synds"
    return(syndsobj)
}