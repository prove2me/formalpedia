-- Prove2me | Definitions.Def_MatrixAnalytic_PHRenewal_Counting
-- name    : MatrixAnalytic_PHRenewal_Counting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:42.010454+00:00
-- url     : https://prove2.me/theorems/09dc0120-0e8e-4f58-817c-a5cdad661d34
-- title:
--   The counting process $(N(x), J(x))$: $P(k,x)$, $\mathrm E[N(x)]$ and the renewal function $R(x)$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a PH representation with $n$ phases and $\boldsymbol t = -T\mathbf 1$. In the PH renewal process the phase process restarts, instantaneously after each absorption, in a phase drawn from $\boldsymbol\tau$; the epochs of absorption are the **renewals**. Let $N(x)$ be the number of renewals in $(0,x]$ and $J(x)$ the phase at time $x$. The pair $(N(x),J(x))$ is a Markov process on $\{0,1,2,\dots\}\times\{1,\dots,n\}$ whose generator has the block form (p. 66)
--   $$Q = \begin{bmatrix} T & \boldsymbol t\cdot\boldsymbol\tau & 0 & \cdots\\ 0 & T & \boldsymbol t\cdot\boldsymbol\tau & \cdots\\ \vdots & & \ddots & \ddots\end{bmatrix}.$$
--
--   1. $Q_K$ denotes the restriction of $Q$ to the levels $0,1,\dots,K$: a finite matrix indexed by (level, phase) pairs with diagonal blocks $T$, blocks $\boldsymbol t\cdot\boldsymbol\tau$ just above the diagonal, and zero blocks elsewhere.
--   2. The matrix $P(k,x)$ has entries
--   $$P_{ij}(k,x) = \mathrm P[N(x)=k,\ J(x)=j \mid N(0)=0,\ J(0)=i] = \bigl[\exp(Q_k x)\bigr]_{(0,i),(k,j)}.$$
--   3. If the initial phase has distribution $\boldsymbol\beta$, the expected number of renewals in $(0,x]$ is
--   $$\mathrm E_{\boldsymbol\beta}[N(x)] = \sum_{k\ge 0} k\,\boldsymbol\beta P(k,x)\mathbf 1.$$
--   4. The **renewal function** of the nondelayed process (initial phase distribution $\boldsymbol\tau$, a renewal at time $0$) is the expected number of renewals in $[0,x]$:
--   $$R(x) = 1 + \sum_{k\ge 0} k\,\boldsymbol\tau P(k,x)\mathbf 1.$$
--
--   These are the probabilistic objects of Sections 3.1–3.2: the renewal density of Theorem 3.1.2 is the derivative of $\mathrm E_{\boldsymbol\beta}[N(x)]$, and Theorem 3.1.4 computes $R(x)$.
--
--   **Formalization Note** The countable-state process $(N(x),J(x))$ is encoded through its transition function on the levels $0,\dots,k$: since the level never decreases, the process killed on leaving level $k$ has the finite generator $Q_k$, and its transition function $\exp(Q_k x)$ (Mathlib's `NormedSpace.exp`) coincides with that of $(N(x),J(x))$ between states of levels $\le k$. Levels are `Fin (k+1)`. The expectation is a `tsum` in $\mathbb R$; the theorems that use it assert its summability rather than assume it. $R(x)$ is defined as an expectation, not by the integral $1+\int_0^x r(u)\,du$, so that Theorems 3.1.2 and 3.1.4 are not definitional.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 62 (renewal function R(x)), p. 65 (N(x), P_ij(k,x)), p. 66 (generator Q of (N(x), J(x)))

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix

namespace MatrixAnalytic.PHRenewal

/-- The generator of the Markov process `{(N(x), J(x))}` on p. 66 (level = number of renewals,
phase = state of the phase process), restricted to the levels `0, …, K`. Block `(ℓ, ℓ)` is `T`,
block `(ℓ, ℓ + 1)` is `t·τ`, all other blocks are `0`. Because the level never decreases, this
is the generator of the process killed when it leaves level `K`, and its transition function
agrees with that of `(N(x), J(x))` on the levels `0, …, K`. -/
def countGen {ι : Type*} [Fintype ι] (τ : ι → ℝ) (T : Matrix ι ι ℝ) (K : ℕ) :
    Matrix (Fin (K + 1) × ι) (Fin (K + 1) × ι) ℝ :=
  fun a b =>
    if (b.1 : ℕ) = (a.1 : ℕ) then T a.2 b.2
    else if (b.1 : ℕ) = (a.1 : ℕ) + 1 then exitVec T a.2 * τ b.2
    else 0

/-- `P(k, x)` (Section 3.2, p. 65): the `n × n` matrix with entries
`P_ij(k, x) = P[N(x) = k, J(x) = j | N(0) = 0, J(0) = i]`, where `N(x)` is the number of renewals
in `(0, x]` and `J(x)` the phase. It is the `((0, i), (k, j))` entry of the transition function
`exp(Q_k x)` of the level-`≤ k` restriction `Q_k = countGen τ T k`. -/
noncomputable def countProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (k : ℕ) (x : ℝ) : Matrix ι ι ℝ :=
  fun i j => NormedSpace.exp (x • countGen τ T k) (0, i) (Fin.last k, j)

/-- The expected number of renewals in `(0, x]`, `E[N(x)] = Σ_{k ≥ 0} k · β P(k, x) 1`, when the
initial phase has distribution `β` (no renewal is counted at time `0`). -/
noncomputable def meanCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * (β ⬝ᵥ (countProb τ T k x *ᵥ fun _ => 1))

/-- The renewal function `R(x)` of the nondelayed PH renewal process (p. 62): the expected number
of renewals in `[0, x]`, counting the renewal at time `0`; the initial phase has distribution
`τ`. -/
noncomputable def renewalFunction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) : ℝ :=
  1 + meanCount τ τ T x

end MatrixAnalytic.PHRenewal


