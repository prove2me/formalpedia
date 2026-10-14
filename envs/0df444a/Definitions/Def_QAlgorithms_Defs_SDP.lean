-- Prove2me | Definitions.Def_QAlgorithms_Defs_SDP
-- name    : QAlgorithms_Defs_SDP
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:47:06.791167+00:00
-- url     : https://prove2.me/theorems/137e0db5-d12d-46df-bf03-f312d6a10387
-- title:
--   Gibbs states, matrix multiplicative weights, semidefinite programs, the MaxCut relaxation
-- statement:
--   Gibbs states, matrix multiplicative weights, semidefinite programs, the MaxCut relaxation
--
--   ### QAlgorithms.gibbsState
--
--   **Inputs.** A finite index set $\iota$ with decidable equality and a complex square matrix $H$ indexed by $\iota$.
--
--   **Definition.** The result is
--
--   $$
--   \mathrm{gibbs}(H) = \big(\operatorname{tr} e^{H}\big)^{-1}\, e^{H},
--   $$
--
--   where $e^{H}$ is the matrix exponential $\sum_{k\ge0} H^k/k!$.
--
--   **Edge cases.**
--
--   - No Hermiticity or other assumption is placed on $H$. Note that the exponent is $+H$, not $-H$.
--   - The inverse uses the convention $0^{-1} = 0$. If $\operatorname{tr} e^H = 0$, the result is the zero matrix.
--   - If $\iota$ is empty, the result is the empty matrix.
--
--   ### QAlgorithms.mmwuIterate
--
--   **Inputs.**
--
--   - A finite index set $\iota$ with decidable equality.
--   - A real number $\eta$.
--   - A sequence $(G_\tau)_{\tau\in\mathbb{N}}$ of complex square matrices indexed by $\iota$.
--   - A natural number $t$.
--
--   **Definition.** The result is
--
--   $$
--   \mathrm{gibbs}\Big(-\eta \sum_{\tau=1}^{t-1} G_\tau\Big) = \frac{\exp\!\big(-\eta \sum_{\tau=1}^{t-1} G_\tau\big)}{\operatorname{tr}\exp\!\big(-\eta \sum_{\tau=1}^{t-1} G_\tau\big)}.
--   $$
--
--   Here $\exp$ is the matrix exponential, and the inverse of the trace uses $0^{-1} = 0$. If the trace is $0$, the result is the zero matrix.
--
--   **Edge cases.**
--
--   - The sum runs over $\tau \in \{1,\dots,t-1\}$, so $G_0$ is never used.
--   - For $t = 0$ or $t = 1$ the sum is empty. The result is then $I/|\iota|$, which is the zero (empty) matrix when $\iota$ is empty.
--   - No assumption is placed on $\eta$ (any sign) or on the $G_\tau$ (Hermitian or not).
--
--   ### QAlgorithms.qRelEntropy
--
--   **Inputs.** A finite index set $\iota$ with decidable equality and two complex square matrices $\rho$ and $\sigma$ indexed by $\iota$.
--
--   **Definition.** The value is the real number
--
--   $$
--   D(\rho\,\|\,\sigma) = \operatorname{Re}\operatorname{tr}\Big( f(\rho) - \rho\,\log(\sigma) - \rho + \sigma \Big), \qquad f(x) = x\log x.
--   $$
--
--   **How $f(\rho)$ and $\log(\sigma)$ are computed.** Both come from the continuous functional calculus with real-valued functions:
--
--   - For a Hermitian matrix with spectral decomposition $\sum_k \lambda_k P_k$, $g$ of the matrix is $\sum_k g(\lambda_k)P_k$.
--   - For a matrix that is not Hermitian (not self-adjoint), the functional calculus returns the zero matrix by convention.
--   - The real logarithm follows the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. Consequently $f(0) = 0$, zero eigenvalues of $\sigma$ contribute $\log 0 = 0$, and negative eigenvalues are allowed.
--
--   **Edge cases.** No positivity, trace, or Hermiticity hypotheses are imposed on $\rho$ or $\sigma$.
--
--   ### QAlgorithms.IsEntropicMirrorDescent
--
--   **Inputs.**
--
--   - A natural number $n$.
--   - A real number $\eta$.
--   - A sequence $(G_t)_{t\in\mathbb{N}}$ of complex $n\times n$ matrices.
--   - A sequence $(\rho_t)_{t\in\mathbb{N}}$ of complex $n\times n$ matrices.
--
--   **Density matrices.** A density matrix is a positive semidefinite matrix of trace $1$. Positive semidefinite means Hermitian with $v^*Mv \ge 0$ for all $v$.
--
--   **The predicate.** $\mathrm{IsEntropicMirrorDescent}(\eta, G, \rho)$ holds iff both of the following are true:
--
--   1. The first iterate is maximally mixed:
--      $$\rho_1 = \tfrac{1}{n} I.$$
--   2. For every integer $t \ge 1$, define
--      $$M_t = \exp\!\big(\log(\rho_t) - \eta\, G_t\big).$$
--      Then $\rho_{t+1}$ is a density matrix, and for every density matrix $\sigma$,
--      $$D(\rho_{t+1}\,\|\,M_t) \le D(\sigma\,\|\,M_t).$$
--      In other words, $\rho_{t+1}$ minimizes $D(\cdot\,\|\,M_t)$ over all density matrices.
--
--   **Definitions used in condition 2.**
--
--   - $\exp$ is the matrix exponential.
--   - $\log(\rho_t)$ is computed by the functional calculus with the real logarithm. It uses the convention $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$, and it is the zero matrix if $\rho_t$ is not Hermitian.
--   - $D(\rho\|\sigma) = \operatorname{Re}\operatorname{tr}\big(\rho\log\rho - \rho\log\sigma - \rho + \sigma\big)$, with the same functional-calculus conventions. In particular, the $\rho\log\rho$ term is zero when $\rho$ is not Hermitian.
--
--   **Edge cases.**
--
--   - $\rho_0$ and $G_0$ are unconstrained and unused.
--   - $\rho_1$ is fixed by the equation, not separately required to be a density matrix. It is one when $n \ge 1$.
--   - No condition is placed on $\eta$ or on the $G_t$.
--   - For $n = 0$ no density matrix exists, since the empty trace is $0 \neq 1$. Condition 2 then fails, so the predicate is unsatisfiable.
--
--   ### QAlgorithms.SDP.PrimalFeasible
--
--   **Inputs.**
--
--   - Natural numbers $n$ and $m$.
--   - Complex $n\times n$ matrices $A_0,\dots,A_{m-1}$.
--   - A real vector $b = (b_0,\dots,b_{m-1}) \in \mathbb{R}^m$.
--   - A complex $n\times n$ matrix $X$.
--
--   **The predicate.** $\mathrm{PrimalFeasible}(A,b,X)$ holds iff both of the following are true:
--
--   1. $X$ is positive semidefinite, i.e. Hermitian with $v^*Xv \ge 0$ for all $v\in\mathbb{C}^n$.
--   2. For every $j \in \{0,\dots,m-1\}$:
--      $$\operatorname{Re}\operatorname{tr}(A_j X) \le b_j.$$
--
--   **Edge cases.**
--
--   - The $A_j$ are not required to be Hermitian. Only the real part of the trace is constrained.
--   - There is no trace normalization of $X$.
--   - If $m = 0$, the predicate just says $X \succeq 0$.
--
--   ### QAlgorithms.SDP.DualFeasible
--
--   **Inputs.**
--
--   - Natural numbers $n$ and $m$.
--   - Complex $n\times n$ matrices $A_0,\dots,A_{m-1}$ and $C$.
--   - A real vector $y \in \mathbb{R}^m$.
--
--   **The predicate.** $\mathrm{DualFeasible}(A,C,y)$ holds iff both of the following are true:
--
--   1. $y_j \ge 0$ for every $j \in \{0,\dots,m-1\}$.
--   2. The matrix
--      $$\sum_{j=0}^{m-1} y_j A_j - C$$
--      is positive semidefinite. That is, it is Hermitian and $v^*\big(\sum_j y_jA_j - C\big)v \ge 0$ for all $v\in\mathbb{C}^n$.
--
--   **Edge cases.**
--
--   - The $A_j$ and $C$ are not individually required to be Hermitian.
--   - If $m = 0$, the condition reads $-C \succeq 0$.
--
--   ### QAlgorithms.SDP.IsDualOptimal
--
--   **Inputs.**
--
--   - Natural numbers $n$ and $m$.
--   - Complex $n\times n$ matrices $A_0,\dots,A_{m-1}$ and $C$.
--   - Real vectors $b \in \mathbb{R}^m$ and $y \in \mathbb{R}^m$.
--
--   **The predicate.** $\mathrm{IsDualOptimal}(A,C,b,y)$ holds iff both of the following are true:
--
--   1. $y$ is dual feasible, meaning:
--      - $y_j \ge 0$ for all $j$, and
--      - $\sum_j y_jA_j - C$ is positive semidefinite (Hermitian with nonnegative quadratic form).
--   2. For every dual-feasible $y' \in \mathbb{R}^m$:
--      $$\sum_{j=0}^{m-1} b_j y_j \le \sum_{j=0}^{m-1} b_j y'_j.$$
--
--   Thus $y$ attains the minimum of the linear objective $b^\top y$ over the dual-feasible set.
--
--   **Edge cases.**
--
--   - If the dual-feasible set is empty, no $y$ satisfies the predicate.
--   - If $b^\top y'$ is unbounded below on the dual-feasible set, no $y$ satisfies the predicate.
--
--   ### QAlgorithms.SDP.picPolytope
--
--   **Inputs.**
--
--   - Natural numbers $n$ and $m$.
--   - Complex $n\times n$ matrices $A_0,\dots,A_{m-1}$ and $C$.
--   - A real vector $b\in\mathbb{R}^m$.
--   - Real numbers $\gamma$ and $\varepsilon$.
--   - A complex $n\times n$ matrix $X$.
--
--   **The set.** $\mathrm{picPolytope}(A,b,C,\gamma,\varepsilon,X)$ is the set of all $y\in\mathbb{R}^m$ satisfying all three of the following:
--
--   $$
--   \sum_{j=0}^{m-1} b_j y_j \le \gamma, \qquad
--   \operatorname{Re}\operatorname{tr}\Big(\Big(\sum_{j=0}^{m-1} y_j A_j - C\Big)X\Big) \ge -\varepsilon, \qquad
--   y_j \ge 0 \text{ for all } j.
--   $$
--
--   **Edge cases.**
--
--   - No hypotheses are imposed on $X$ (it need not be positive semidefinite or Hermitian), on the signs of $\gamma$ and $\varepsilon$, or on the matrices $A_j$ and $C$.
--   - The set may be empty.
--   - If $m = 0$, the set is the single point of $\mathbb{R}^0$ when $0 \le \gamma$ and $-\operatorname{Re}\operatorname{tr}(CX) \ge -\varepsilon$, and it is empty otherwise.
--
--   ### QAlgorithms.SDP.IsPICOracle
--
--   This is a predicate on an "oracle" $O$. The ingredients are:
--
--   - dimensions $n, m \in \mathbb{N}$;
--   - complex $n\times n$ matrices $A_1,\dots,A_m$ (indexed by $j \in \{0,\dots,m-1\}$) and $C$;
--   - a real vector $b \in \mathbb{R}^m$ and reals $\gamma, \varepsilon, w$;
--   - a function $O$ that sends each complex $n\times n$ matrix $X$ either to "no answer" ($\mathrm{none}$) or to a vector $y \in \mathbb{R}^m$.
--
--   No assumptions are made on $A_j$ or $C$: they need not be Hermitian. For a matrix $X$, the set $\mathcal{P}(X)$ (the definition `picPolytope`) is
--
--   $$\mathcal{P}(X) = \Big\{ y \in \mathbb{R}^m \;:\; \sum_j b_j y_j \le \gamma,\;\; \operatorname{Re}\operatorname{tr}\Big(\big(\textstyle\sum_j y_j A_j - C\big) X\Big) \ge -\varepsilon,\;\; y_j \ge 0 \text{ for all } j \Big\}.$$
--
--   $\mathrm{IsPICOracle}(A,b,C,\gamma,\varepsilon,w,O)$ holds iff, for every positive semidefinite complex $n\times n$ matrix $X$ (Hermitian with $v^*Xv \ge 0$ for all $v$), both of the following hold:
--
--   1. $O(X) = \mathrm{none}$ if and only if $\mathcal{P}(X) = \emptyset$.
--   2. Whenever $O(X) = y$, we have $y \in \mathcal{P}(X)$ and
--   $$\Big\| \sum_j y_j A_j - C \Big\|_{\mathrm{op}} \le w,$$
--   where $\|\cdot\|_{\mathrm{op}}$ is the $\ell^2$ operator norm (largest singular value).
--
--   Edge cases:
--
--   - Nothing is required of $O$ on matrices $X$ that are not positive semidefinite.
--   - Every such oracle must answer whenever $\mathcal{P}(X) \neq \emptyset$, and every answer must satisfy the norm bound. So if $w < 0$, the predicate can only hold when $\mathcal{P}(X)$ is empty for every positive semidefinite $X$.
--   - Taking $X = 0$: $\mathcal{P}(0)$ is empty exactly when $\varepsilon < 0$ or no $y \ge 0$ has $b\cdot y \le \gamma$.
--
--   ### QAlgorithms.SDP.mmwuLoss
--
--   The inputs are:
--
--   - complex $n\times n$ matrices $A_1,\dots,A_m$ and $C$;
--   - a real $w$;
--   - a finite list $ys = (y^{(0)}, y^{(1)}, \dots, y^{(L-1)})$ of vectors in $\mathbb{R}^m$;
--   - a natural number $\tau$.
--
--   The output is the complex $n\times n$ matrix
--
--   $$\mathrm{mmwuLoss}(A,C,w,ys,\tau) = w^{-1}\Big( \sum_{j} \tilde y_j\, A_j - C \Big).$$
--
--   Here $\tilde y$ is the list entry at position $\tau - 1$ (0-based), i.e. the $\tau$-th element counting from 1, if that position exists; otherwise $\tilde y$ is the zero vector. The subtraction $\tau - 1$ is natural-number subtraction, so $\tau = 0$ and $\tau = 1$ both select the first element $y^{(0)}$.
--
--   Edge cases:
--
--   - If $\tau - 1 \ge L$ (in particular when the list is empty), the result is $-w^{-1} C$.
--   - If $w = 0$, then $w^{-1}$ is taken as $0$ and the result is the zero matrix.
--
--   ### QAlgorithms.SDP.mmwuRun
--
--   The inputs are complex $n\times n$ matrices $A_1,\dots,A_m$ and $C$, reals $R, \eta, w$, and an oracle $O$ that sends each complex $n\times n$ matrix to either $\mathrm{none}$ or a vector in $\mathbb{R}^m$.
--
--   $\mathrm{mmwuRun}(k)$ is defined by recursion on $k \in \mathbb{N}$. Its value is one of two kinds:
--
--   - a "halt" value carrying a complex $n\times n$ matrix $X$;
--   - a "continue" value carrying a list $ys$ of vectors in $\mathbb{R}^m$.
--
--   **Base case.** $\mathrm{mmwuRun}(0)$ is "continue" with the empty list.
--
--   **Step $k+1$.**
--
--   - If $\mathrm{mmwuRun}(k)$ is "halt with $X$", then so is $\mathrm{mmwuRun}(k+1)$.
--   - If $\mathrm{mmwuRun}(k)$ is "continue with $ys$", form the matrix
--   $$X_{k+1} = R\cdot \rho_{k+1}, \qquad \rho_{k+1} = \frac{e^{H}}{\operatorname{tr} e^{H}}, \qquad H = -\eta \sum_{\tau=1}^{k} G_\tau, \qquad G_\tau = w^{-1}\Big(\sum_j y^{(\tau-1)}_j A_j - C\Big).$$
--   Here $e^{H}$ is the matrix exponential, and $(\operatorname{tr} e^H)^{-1}$ is read as $0$ if the trace vanishes.
--     - If $O(X_{k+1}) = \mathrm{none}$, the result is "halt with $X_{k+1}$".
--     - If $O(X_{k+1}) = y$, the result is "continue with $ys$ extended by $y$ at the end".
--
--   By induction, a "continue" value at stage $k$ carries a list of length exactly $k$. So $G_\tau$ for $\tau = 1, \dots, k$ uses the $\tau$-th entry of that list, which is the `mmwuLoss` value at index $\tau$. For $k = 0$ the sum is empty, $H = 0$, and $\rho_1 = I/n$ (for $n \ge 1$).
--
--   ### QAlgorithms.SDP.mmwuSDP
--
--   The inputs are complex $n\times n$ matrices $A_1,\dots,A_m$ and $C$, reals $R, \varepsilon, w$, and an oracle $O$ as above. The output is either a complex $n\times n$ matrix (left alternative) or a vector in $\mathbb{R}^m$ (right alternative).
--
--   Set
--
--   $$T = \Big\lceil \frac{9\, w^2 R^2 \ln n}{\varepsilon^2} \Big\rceil \in \mathbb{N}, \qquad \eta = \sqrt{\frac{\ln n}{T}}.$$
--
--   The conventions are:
--
--   - the ceiling of a negative number is $0$;
--   - $\varepsilon^{-2}$ is $0$ when $\varepsilon = 0$;
--   - $T^{-1}$ is $0$ when $T = 0$;
--   - $\ln 0 = 0$ and $\ln 1 = 0$, so $T = 0$ and $\eta = 0$ whenever $n \le 1$, $\varepsilon = 0$, $w = 0$ or $R = 0$.
--
--   Run the procedure `mmwuRun` above with parameters $(A, C, R, \eta, w, O)$ for $T$ stages.
--
--   - If it ends in "halt with $X$", the output is the matrix $X$.
--   - If it ends in "continue with $ys = (y^{(0)},\dots,y^{(T-1)})$", the output is the vector
--   $$\frac{1}{T}\sum_{t} y^{(t)} + \frac{\varepsilon}{R}\, e_0,$$
--   where $e_0 \in \mathbb{R}^m$ has a $1$ in its first coordinate (index $0$) and $0$ elsewhere.
--
--   Edge cases:
--
--   - $R^{-1}$ is $0$ when $R = 0$.
--   - If $m = 0$, the vector is the empty vector.
--   - If $T = 0$, the run returns "continue" with the empty list, and the output is $\frac{\varepsilon}{R} e_0$.
--
--   ### QAlgorithms.SDP.genPicPolytope
--
--   The inputs are $m \in \mathbb{N}$, vectors $b, a \in \mathbb{R}^m$, and reals $\gamma, r, c$. The definition gives the set
--
--   $$\Big\{ y \in \mathbb{R}^m \;:\; \sum_j b_j y_j \le \gamma,\;\; \sum_j y_j \le r,\;\; \sum_j a_j y_j \ge c,\;\; y_j \ge 0 \text{ for all } j \Big\}.$$
--
--   All inequalities are non-strict. For $m = 0$, all sums are $0$, so the set is the single point $\mathbb{R}^0$ when $0 \le \gamma$, $0 \le r$ and $c \le 0$, and empty otherwise.
--
--   ### QAlgorithms.SDP.cHat
--
--   For a complex $n\times n$ matrix $C$,
--
--   $$\hat C = \frac{1}{\|C\|_F}\, C, \qquad \|C\|_F = \Big(\sum_{i,j} |C_{ij}|^2\Big)^{1/2},$$
--
--   where $\|C\|_F$ is the Frobenius norm. If $C = 0$, the inverse is read as $0$, and $\hat C = 0$.
--
--   ### QAlgorithms.SDP.maxCutF
--
--   The inputs are a complex $n\times n$ matrix $C$, a real $\gamma$, and a complex $n\times n$ matrix $\rho$. No density-matrix assumption is made on $\rho$. The value is the real number
--
--   $$\max\Big( \gamma - \operatorname{Re}\operatorname{tr}(\hat C \rho),\;\; \sum_{j=0}^{n-1} \big| \operatorname{Re}\rho_{jj} - \tfrac{1}{n} \big| \Big),$$
--
--   where $\hat C = C/\|C\|_F$ is the normalized matrix defined in `cHat` above (equal to $0$ if $C = 0$).
--
--   For $n = 0$, the sum is empty and the value is $\max(\gamma - 0, 0)$.
--
--   ### QAlgorithms.SDP.maxCutSubgrad
--
--   The inputs are:
--
--   - a complex $n\times n$ matrix $C$;
--   - reals $\gamma, \varepsilon$;
--   - a real number $e_C$ (the argument `estC`);
--   - a real vector $d = (d_0,\dots,d_{n-1})$ (the argument `estD`).
--
--   Write $\Delta = \sum_j |d_j - \tfrac1n|$. The output is a complex $n\times n$ matrix, defined by cases:
--
--   - If $\max(\gamma - e_C,\; \Delta) \le \tfrac{3\varepsilon}{4}$, the output is the zero matrix.
--   - Otherwise, if $\Delta \le \gamma - e_C$, the output is $-\hat C$, where $\hat C = C/\|C\|_F$ is the Frobenius-normalized matrix from `cHat` (or $0$ if $C = 0$).
--   - Otherwise, the output is the diagonal matrix with entries
--   $$D_{jj} = \begin{cases} 1 & \text{if } d_j > \tfrac1n,\\ -1 & \text{if } d_j < \tfrac1n,\\ 0 & \text{if } d_j = \tfrac1n.\end{cases}$$
--
--   The comparisons are exactly as written: non-strict $\le$ in the first two tests, strict in the diagonal entries. For $n = 0$, the term $\tfrac1n$ is read as $0$ and $\Delta = 0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/SDP.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
/-!
# Gibbs states, matrix multiplicative weights, semidefinite programs, the MaxCut relaxation
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 7–8. Matrix functions: the exponential is Mathlib's power series
`NormedSpace.exp` (no sign or time factor: the source's `exp(H)`); the logarithm and `x log x` of
Hermitian matrices use Mathlib's continuous functional calculus `cfc` (real functions applied to
the eigenvalues). Iteration indices are the source's, 1-based.
-/

namespace QAlgorithms

open scoped ComplexOrder

/-- Nannicini p.170, Def. 7.34 (and p.183, Alg. 6): the Gibbs state `exp(H) / Tr(exp(H))` of the
Hamiltonian `H`, with the plain matrix exponential. For Hermitian `H` the trace is positive. -/
noncomputable def gibbsState {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (NormedSpace.exp H).trace⁻¹ • NormedSpace.exp H

/-- Nannicini p.182 (Prop. 8.7) and p.183 (Alg. 6): the matrix multiplicative weights iterate
`ρ^{(t)} = exp(−η Σ_{τ=1}^{t−1} G^{(τ)}) / Tr(…)`, i.e. the Gibbs state of `H^{(t)}` with
`H^{(1)} = 0` and `H^{(t+1)} = H^{(t)} − η G^{(t)}`. 1-based: `t ≥ 1` and `G τ` for `τ ≥ 1`
(`G 0` is never read); `mmwuIterate η G 1 = I/n`. -/
noncomputable def mmwuIterate {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ)
    (G : ℕ → Matrix ι ι ℂ) (t : ℕ) : Matrix ι ι ℂ :=
  gibbsState (-(η : ℂ) • ∑ τ ∈ Finset.Ico 1 t, G τ)

/-- Nannicini p.180 (Def. 8.2) and p.182 (§8.1.2): the Bregman divergence of the von Neumann
negative entropy `h(ρ) = Tr(ρ log ρ − ρ)`, the quantum relative entropy
`D_h(ρ‖σ) = Tr(ρ log ρ − ρ log σ − ρ + σ)` (real part). `ρ log ρ` is the functional calculus of
`x ↦ x log x` (`0` at `0`, as `Real.log 0 = 0`). Meaningful for Hermitian `ρ ⪰ 0` and `σ ≻ 0`
(Mathlib's `cfc` is `0` on non-Hermitian input, and `Real.log` is `0` on `x ≤ 0`); every use has a
density matrix `ρ` and a matrix exponential `σ`. -/
noncomputable def qRelEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) ρ - ρ * cfc Real.log σ - ρ + σ).trace.re

/-- Nannicini p.181 (Eq. (8.8)) and p.182 (§8.1.2): `ρ` is a sequence of iterates of mirror
descent over the density matrices `K = S^n_{+,1}` with the mirror map `h` (`∇h = log`,
`(∇h)^{-1} = exp`), step `η` and subgradients `G t`, from `ρ^{(1)} = I/n`:
`ρ^{(t+1)} ∈ argmin_{σ ∈ K} D_h(σ ‖ exp(log ρ^{(t)} − η G^{(t)}))` for every `t ≥ 1` (the argmin
is a membership condition; attainment is part of it). -/
def IsEntropicMirrorDescent {n : ℕ} (η : ℝ) (G : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℕ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ 1 = (n : ℂ)⁻¹ • 1 ∧
    ∀ t ≥ 1, IsDensityMatrix (ρ (t + 1)) ∧
      ∀ σ : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix σ →
        qRelEntropy (ρ (t + 1)) (NormedSpace.exp (cfc Real.log (ρ t) - (η : ℂ) • G t)) ≤
          qRelEntropy σ (NormedSpace.exp (cfc Real.log (ρ t) - (η : ℂ) • G t))

namespace SDP

/-- Nannicini p.178, (P-SDP): `X` is feasible for `max Tr(CX)` s.t. `Tr(A^{(j)} X) ≤ b_j`
(`j = 1, …, m`, here 0-based) and `X ⪰ 0`. The objective `(C * X).trace.re` is written inline. -/
def PrimalFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  X.PosSemidef ∧ ∀ j, (A j * X).trace.re ≤ b j

/-- Nannicini p.178, (D-SDP): `y` is feasible for `min b^⊤ y` s.t.
`Σ_j y_j A^{(j)} − C ⪰ 0` and `y ≥ 0`. The objective `Σ_j b_j y_j` is written inline. -/
def DualFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (∑ j, (y j : ℂ) • A j - C).PosSemidef

/-- Nannicini p.192, assumption (c): `y` is an optimal solution of (D-SDP): dual feasible with
`b^⊤ y ≤ b^⊤ y'` for every dual feasible `y'`. -/
def IsDualOptimal {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (y : Fin m → ℝ) : Prop :=
  DualFeasible A C y ∧ ∀ y', DualFeasible A C y' → ∑ j, b j * y j ≤ ∑ j, b j * y' j

/-- Nannicini p.188, Def. 8.11, Eq. (8.16): the primal-infeasibility-certificate polytope
`P_ε(X) = {y ∈ ℝ^m : b^⊤ y ≤ γ, Tr((Σ_j y_j A^{(j)} − C) X) ≥ −ε, y ≥ 0}` (real part of the
trace); `ε = 0` is allowed, as used in Prop. 8.19. -/
def picPolytope {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) (γ ε : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Set (Fin m → ℝ) :=
  {y | ∑ j, b j * y j ≤ γ ∧ ((∑ j, (y j : ℂ) • A j - C) * X).trace.re ≥ -ε ∧ ∀ j, 0 ≤ y j}

/-- Nannicini p.188 (Def. 8.11) and p.189 (Def. 8.13): `O` is a PIC-Oracle_ε of width at most
`w`: on every `X ⪰ 0` (the inputs the source calls it on), it returns "failure" (`none`) iff
`P_ε(X) = ∅`, and every vector `y` it returns lies in `P_ε(X)` and satisfies
`‖Σ_j y_j A^{(j)} − C‖ ≤ w` (operator norm). -/
def IsPICOracle {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) (γ ε w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef →
    (O X = none ↔ picPolytope A b C γ ε X = ∅) ∧
      ∀ y, O X = some y → y ∈ picPolytope A b C γ ε X ∧ specNorm (∑ j, (y j : ℂ) • A j - C) ≤ w

/-- Nannicini p.190, Alg. 7, line 7: the loss matrices `M^{(τ)} = (1/w)(Σ_j y^{(τ)}_j A^{(j)} − C)`
built from the oracle answers `ys = [y^{(1)}, …, y^{(t)}]` (1-based: `τ` reads `ys[τ − 1]`). -/
noncomputable def mmwuLoss {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (w : ℝ) (ys : List (Fin m → ℝ)) (τ : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((w : ℂ)⁻¹) • (∑ j, ((ys.getD (τ - 1) 0) j : ℂ) • A j - C)

/-- Nannicini p.190, Alg. 7, lines 2–9: the state of the loop after `k` iterations with step `η`:
either it has stopped with the primal candidate `R ρ^{(t)}` (`inl`) at the first iteration `t`
where the oracle `O` answers "failure", or (`inr`) it holds the answers `[y^{(1)}, …, y^{(k)}]`.
Iteration `t` computes `ρ^{(t)} = mmwuIterate η M t` (`ρ^{(1)} = I/n`) from the losses so far and
queries `O (R ρ^{(t)})`. -/
noncomputable def mmwuRun {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (R η w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    ℕ → Matrix (Fin n) (Fin n) ℂ ⊕ List (Fin m → ℝ)
  | 0 => Sum.inr []
  | k + 1 =>
      match mmwuRun A C R η w O k with
      | Sum.inl X => Sum.inl X
      | Sum.inr ys =>
          match O ((R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1)) with
          | none => Sum.inl ((R : ℂ) • mmwuIterate η (mmwuLoss A C w ys) (k + 1))
          | some y => Sum.inr (ys ++ [y])

/-- Nannicini p.189 (Def. 8.13) and p.190 (Alg. 7): the output of the MMWU algorithm for SDP with
trace bound `R`, tolerance `ε`, width bound `w` and the oracle `O` (the source's
PIC-Oracle_{ε/3}; its specification is a hypothesis of the theorem):
`T = ⌈9 w² R² ln n / ε²⌉`, `η = √(ln n / T)`; run `T` iterations of `mmwuRun`; on a failure return
`inl (R ρ^{(t)})` (the primal candidate, before the rescaling of Lem. 8.12, which the theorem
states), otherwise return `inr ((1/T) Σ_t y^{(t)} + (ε/R) e_1)`, with `e_1` the first coordinate
vector (index `0`; the source's `A^{(1)} = I`). Degenerate case `n = 1`: `T = 0`, no iteration,
and the output is `inr ((ε/R) e_1)`. -/
noncomputable def mmwuSDP {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin n) (Fin n) ℂ) (R ε w : ℝ)
    (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    Matrix (Fin n) (Fin n) ℂ ⊕ (Fin m → ℝ) :=
  let T : ℕ := ⌈9 * w ^ 2 * R ^ 2 * Real.log n * (ε ^ 2)⁻¹⌉₊
  let η : ℝ := Real.sqrt (Real.log n * (T : ℝ)⁻¹)
  match mmwuRun A C R η w O T with
  | Sum.inl X => Sum.inl X
  | Sum.inr ys => Sum.inr ((T : ℝ)⁻¹ • ys.sum + (ε * R⁻¹) • fun j : Fin m => if (j : ℕ) = 0 then 1 else 0)

/-- Nannicini p.192, Def. 8.18, Eq. (8.23): the generalized primal-infeasibility-certificate
polytope `P̂(a, c) = {y ∈ ℝ^m : b^⊤ y ≤ γ, Σ_j y_j ≤ r, Σ_j a_j y_j ≥ c, y ≥ 0}`. -/
def genPicPolytope {m : ℕ} (b : Fin m → ℝ) (γ r : ℝ) (a : Fin m → ℝ) (c : ℝ) : Set (Fin m → ℝ) :=
  {y | ∑ j, b j * y j ≤ γ ∧ ∑ j, y j ≤ r ∧ ∑ j, a j * y j ≥ c ∧ ∀ j, 0 ≤ y j}

/-- Nannicini p.199, §8.4.1: the normalized MaxCut cost matrix `Ĉ = C / ‖C‖_F` (frozen
`frobNorm`). Junk value `0` at `C = 0`; statements assume `C ≠ 0`. -/
noncomputable def cHat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((frobNorm C)⁻¹ : ℂ) • C

/-- Nannicini p.200, Eq. (8.26): `f_γ(ρ) = max{γ − Tr(Ĉρ), Σ_j |ρ_jj − 1/n|}` (real parts, the
values on Hermitian `ρ`). -/
noncomputable def maxCutF {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  max (γ - (cHat C * ρ).trace.re) (∑ j, |(ρ j j).re - (n : ℝ)⁻¹|)

/-- Nannicini pp.200–201, §8.4.2: the inexact subgradient computed from the estimates `estC` of
`Tr(Ĉρ)` and `estD j` of `ρ_jj`: with `u = γ − estC` and `v = Σ_j |estD_j − 1/n|`, return `0` if
`max{u, v} ≤ 3ε/4`; otherwise `−Ĉ` if `u` attains the maximum (`v ≤ u`); otherwise
`Σ_j (I(estD_j > 1/n) − I(1/n > estD_j)) E_jj`. -/
noncomputable def maxCutSubgrad {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ ε : ℝ) (estC : ℝ)
    (estD : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  if max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹ then 0
  else if ∑ j, |estD j - (n : ℝ)⁻¹| ≤ γ - estC then -cHat C
  else Matrix.diagonal fun j =>
    if (n : ℝ)⁻¹ < estD j then 1 else if estD j < (n : ℝ)⁻¹ then -1 else 0

end SDP

/-! ### Sanity tests -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    gibbsState (0 : Matrix ι ι ℂ) = ((Fintype.card ι : ℂ))⁻¹ • 1 := by
  simp [gibbsState, NormedSpace.exp_zero, Matrix.trace_one]

example {ι : Type*} [Fintype ι] [DecidableEq ι] (η : ℝ) (G : ℕ → Matrix ι ι ℂ) :
    mmwuIterate η G 1 = gibbsState 0 := by
  simp [mmwuIterate]

example {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ)
    (R η w : ℝ) (O : Matrix (Fin n) (Fin n) ℂ → Option (Fin m → ℝ)) :
    SDP.mmwuRun A C R η w O 0 = Sum.inr [] := rfl

example {m : ℕ} (b : Fin m → ℝ) (γ r c : ℝ) (hc : 0 < c) :
    SDP.genPicPolytope b γ r 0 c = ∅ := by
  ext y; simp [SDP.genPicPolytope]; intros; linarith

example {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (γ ε estC : ℝ) (estD : Fin n → ℝ)
    (h : max (γ - estC) (∑ j, |estD j - (n : ℝ)⁻¹|) ≤ 3 * ε * 4⁻¹) :
    SDP.maxCutSubgrad C γ ε estC estD = 0 := by
  simp [SDP.maxCutSubgrad, h]

end QAlgorithms


