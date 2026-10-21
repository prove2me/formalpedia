-- Prove2me | Definitions.Def_MatrixAnalytic_PH_Discrete
-- name    : MatrixAnalytic_PH_Discrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:48.873909+00:00
-- url     : https://prove2.me/theorems/bdf2c298-1bba-4228-bfea-9f560ec4edc4
-- title:
--   Discrete PH representations $\mathrm{PH}_d(\tau, T)$, the absorbing transition matrix, and the law of the absorption time
-- statement:
--   Fix a finite set of **phases** and adjoin an absorbing state $0$. Let $T$ be a real matrix indexed by the phases and $\boldsymbol\tau$ a real row vector indexed by the phases. Set
--   $$\boldsymbol t = \mathbf 1 - T\mathbf 1, \qquad \tau_0 = 1 - \boldsymbol\tau\mathbf 1,$$
--   so that $\boldsymbol t + T\mathbf 1 = \mathbf 1$ and $\tau_0 + \boldsymbol\tau\mathbf 1 = 1$. Following p. 47 of Latouche and Ramaswami, the file defines:
--
--   1. $(\boldsymbol\tau, T)$ is a **discrete PH representation** $\mathrm{PH}_d(\boldsymbol\tau, T)$ if $T_{ij} \ge 0$ and $t_i \ge 0$ for all phases $i, j$, and $(\tau_0, \boldsymbol\tau)$ is a probability vector ($\boldsymbol\tau \ge 0$, $\tau_0 \ge 0$).
--   2. The **transition probability matrix** of the absorbing discrete-time Markov chain on $\{0\} \cup \{\text{phases}\}$:
--   $$P = \begin{bmatrix} 1 & \mathbf 0 \\ \boldsymbol t & T \end{bmatrix}.$$
--   3. The **distribution function** of the absorption time $X$ into $0$ of the chain started with distribution $(\tau_0, \boldsymbol\tau)$: since $0$ is absorbing, $X \le k$ exactly when the chain is in $0$ at step $k$, so
--   $$\mathrm P[X \le k] = \tau_0 (P^k)_{00} + \sum_i \tau_i (P^k)_{i0}, \qquad k \ge 0.$$
--   4. Its **probability mass function**: $\mathrm P[X = 0] = \mathrm P[X \le 0]$ and $\mathrm P[X = k+1] = \mathrm P[X \le k+1] - \mathrm P[X \le k]$.
--
--   These are the objects of Theorem 2.5.3 and of the closure Theorems 2.6.1, 2.6.2, 2.6.4 and 2.6.5.
--
--   **Formalization Note** The phase set is an arbitrary finite type `ι` with decidable equality; the absorbing state $0$ is `none` in `Option ι`. The $k$-step transition probabilities of the finite chain are the entries of the matrix power $P^k$, so the law of $X$ is computed from $P^k$ without a path space. "$X$ is $\mathrm{PH}_d(\boldsymbol\tau, T)$" is expressed by these two functions of $k$; the closure theorems compare them for different representations.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 47, Section 2.5 (definition of PH_d(τ, T)); p. 49 (the powers P^k)

import Mathlib

open Matrix

namespace MatrixAnalytic.PH

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exit-probability column vector `t = 𝟙 − T𝟙` of a substochastic matrix `T`, i.e. the vector
determined by `t + T𝟙 = 𝟙` (Latouche–Ramaswami, p. 47). -/
def dExitProbs (T : Matrix ι ι ℝ) : ι → ℝ :=
  fun i => 1 - (T *ᵥ fun _ => (1 : ℝ)) i

/-- The mass `τ₀ = 1 − τ𝟙` that the initial vector `(τ₀, τ)` puts on the absorbing state 0. -/
def dInitAtom (τ : ι → ℝ) : ℝ :=
  1 - ∑ i, τ i

/-- `(τ, T)` is a discrete PH representation `PH_d(τ, T)` (p. 47): `T_ij ≥ 0`, `t_i ≥ 0` with
`t + T𝟙 = 𝟙`, and `(τ₀, τ)` is a probability vector on `{0} ∪ phases` (`τ ≥ 0`, `τ₀ ≥ 0`). -/
structure IsPHdRep (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Prop where
  entry_nonneg : ∀ i j, 0 ≤ T i j
  exitProbs_nonneg : ∀ i, 0 ≤ dExitProbs T i
  init_nonneg : ∀ i, 0 ≤ τ i
  initAtom_nonneg : 0 ≤ dInitAtom τ

/-- The transition probability matrix `P = [[1, 0], [t, T]]` of the absorbing discrete-time Markov
chain on `{0} ∪ phases` (p. 47); the absorbing state 0 is `none`, phase `i` is `some i`. -/
def dTransMat (T : Matrix ι ι ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.of fun a b =>
    match a, b with
    | none, none => 1
    | none, some _ => 0
    | some i, none => dExitProbs T i
    | some i, some j => T i j

/-- The initial probability vector `(τ₀, τ)` on `{0} ∪ phases`. -/
def dInitDist (τ : ι → ℝ) : Option ι → ℝ
  | none => dInitAtom τ
  | some i => τ i

/-- The distribution function `P[X ≤ k]` of the absorption time `X` of the chain started with
`(τ₀, τ)`: since 0 is absorbing, `X ≤ k` iff the chain is in 0 at step `k`, so
`P[X ≤ k] = Σ_a (τ₀, τ)_a (P^k)_{a0}`. -/
def dcdf (τ : ι → ℝ) (T : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  ∑ a, dInitDist τ a * (dTransMat T ^ k) a none

/-- The probability mass function of the absorption time `X`: `P[X = 0] = P[X ≤ 0]` and
`P[X = k + 1] = P[X ≤ k + 1] − P[X ≤ k]`. -/
def dpmf (τ : ι → ℝ) (T : Matrix ι ι ℝ) : ℕ → ℝ
  | 0 => dcdf τ T 0
  | k + 1 => dcdf τ T (k + 1) - dcdf τ T k

end MatrixAnalytic.PH


