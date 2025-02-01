\section{Introduction}

The "Hausdorff  rank" of a linear order is an ordinal that measure its  complexity.  
We denote by $\Hr[\alpha]$ the set of linear orders  of the Hausdorff  rank $\alpha$ and by $\Hr$ the set of linear orders  with defined Hausdorff  rank,  i.e., $\Hr:=\cup\Hr[\alpha]$.

\begin{theorem}[Decidability]  \label{th:dec}
The monadic theory of $\Hr$ is decidable. 
\end{theorem} 
\begin{theorem}[Definable  model property]\label{th:sm}
  If $\vp$ is satisfiable in a $\Hr$, then 
 % \item[Small model property] $\psi$ is satisfiable in $BP_\alpha$ for $\alpha<\om^\om$.
  %\item[Regular Model]
   there is $\psi$ which has a unique model $T$  and $\vp $ is satisfiable in $T$.
Moreover,  the Hausdorff rank of $T$ is finite. 
% 
%  Moreover, $
%  \alpha<\om^\om$ and $FS$ is $\MSO[<]$-definable in $\alpha$. 
   \end{theorem}
  

\begin{theorem}[Monadic Theory]\label{th:code}
The monadic theory of  $\Hr[\om]$  is decidable,
The monadic theory of  $\Hr[\om]$ is the same as the monadic theory of  $\Hr[\alpha] $  for every $\alpha\geq \om$.  
\end{theorem} 

%A subset $X$ of a tree is downward closed if whenever $v\in X$, then all the nodes  on the path from the root of $T$ to $v$ are in $X$.
Given an ordinal $\alpha$, for an interval $I$, let $\intro*\hrank\alpha(I)$ express that   ``$I$ has  "Hausdorff  rank"~$\alpha$.'' 
We denote by  $\intro*\MSO[\hrank\alpha]$ monadic second-order logic  extended with the new predicate $\hrank\alpha(-)$. We prove:
%\begin{theorem}\label{theorem:main-trees}

\begin{theorem}\label{th:main-hr} %
	For all countable ordinals $\alpha$,  
	 the $\MSO[\hrank\alpha]$-theory of the $\Hr$ is decidable,
	 \end{theorem}

\section{Proof Plan of \Cref{th:main-hr}}
We say that an interval $I$ is  Major  of $\Hr$ $\alpha$ ($\Mhr_\alpha(I)$), if $I$ has Hausdorff  rank $\alpha$ and $\forall x,y\in I$ the Hausdorff  rank of $[x,y]$ is less than $\alpha$. 
%
%Define $x\sim y$ if there is $I$  such that $\Mhr_\alpha(I)$  such that $x,y\in I$ or $[x,y]\cap I=\emptyset$
%for every $I$  such that $\Mhr_\alpha(I)$. 
\begin{dfn}[$\sim$-equivalence]
  $x\sim y$ if either
  \begin{enumerate}
    \item there is $I$  such that $\Mhr_\alpha(I)$  and  $x,y\in I$, or 
    \item $[x,y]\cap I=\emptyset$
for every $I$  such that $\Mhr_\alpha(I)$. 
  \end{enumerate}
  %there is $I$  such that $\Mhr_\alpha(I)$)  such that $x,y\in I$ or $[x,y]\cap I=\emptyset$
%for every $I$  such that $\Mhr_\alpha(I)$. 
\end{dfn}
\begin{examp}
  Find $\sim$ for $\alpha=1$ and $L:=\om^2 +25 +Z +3 +(-\om)+(-\om)$.
\end{examp}
\begin{lemma} The $\sim$ equivalence classes of $L$  are intervals. If $J$ is an equivalence class %of $x$
 then
either $\Mhr_\alpha(J)$ or $J\in \Hr_\beta$ for $\beta<\alpha$.
  
\end{lemma}
We call $\sim$-class big/small if \dots

Note that $\sim$ is $\MSO[\hrank\alpha]$-definable but we are not going to use this fact.
 %\footnote{Can you prove Composition theorem
%for  $\MSO[\hrank\alpha]$.}. 
 \begin{lemma}[Translation]\label{lem:translation} There is an algorithm that 
 for every $\vp (\vX)\in \MSO[\hrank\alpha]$ constructs  $\psi(\vX, P_{big},P_\sm)\in \MSO$ % $\psi(\vX, P_\om,P_{-\om},P_Z,P_\sm)\in \MSO$
 such that $\dots$
    
 \end{lemma}
 
%Properties of $\sim$:
 
 If $I_1$ and $I_2$ are successor $\sim$-classes,
 then either $I_1$ does not have maximal or $I_2$ does not have minimal.
 
 Four types of $\sim$-classes: no maximal no minimal of type $Z$, maximal no minimal of type $-\om$, minimum no maximal of type $\om$, small\footnote{Explain these types of intervals $\om$, $-\om$, $Z$ sums.}.
 \begin{lemma}[Properties of $\sim$]\label{lem:properties}
Assume  $I_1$ and $I_2$ are successor $\sim$-classes.
   \begin{enumerate}
     \item % If $I_1$ and $I_2$ are successor $\sim$-classes,
% then 
Either $I_1$ does not have maximal or $I_2$ does not have minimal.
 
     \item If $I_1$ is small, then $I_2$ is not small.
     \item  If $I_1$ is small, then $I_2$ is not of type $\om$.
     \item  If $I_2$ is small, then $I_1$ is not of type $-\om$.
   \end{enumerate}
 \end{lemma}
  
 \begin{lemma} For each  of these types $\dag$, the monadic theory of the interval of type $\dag$ is decidable.
 \end{lemma}
 Let $L$ be a scattered (general) linear order labeled by four types of $\dag\in \{\om.-\om,Z,\mathit{small}\}$. %  and $n$-types.
 We say that the labeling is consistent if $\dots$
 \begin{lemma}
   Assume that $L$ is consistently labeled linear order and $L_i$ for ($i\in L$) be a family of linear orders which is consistent with the labelling of $L$.
   Then the $\sim$-classes on $\sum_{i\in L} L_i$ are $\dots$
 \end{lemma}
 \begin{lemma}[Translation]\label{lem:translation} There is an algorithm that 
 for every $\vp (\vX)\in \MSO[\hrank\alpha]$ constructs $\psi(\vX, P_\om,P_{-\om},P_Z,P_\sm)\in \MSO$
 such that $\dots$
    
 \end{lemma}
An $n$-type  $\sigma$ is satisfiable if there is a consistent labellingbe the corresponding $n$-type.