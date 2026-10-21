-- Prove2me | Definitions.Def_MatrixAnalytic_ProductForm_QBD
-- name    : MatrixAnalytic_ProductForm_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:40.264604+00:00
-- url     : https://prove2.me/theorems/97e46661-3c58-4412-9367-1161a8c71413
-- title:
--   Continuous-time QBD (6.19): generator, levels, the rate matrix R and sojourn matrix N of Theorem 6.4.1, and level–phase independence
-- statement:
--   Fix a countable set of phases $\iota$ (finite or infinite) and real matrices $B, A_0, A_1, A_2$ indexed by $\iota\times\iota$. The **continuous-time QBD** with these blocks is the Markov process on the states $(n,i)$, $n\ge 0$ (the level) and $i\in\iota$ (the phase), with block-tridiagonal generator
--   $$Q=\begin{bmatrix} B & A_0 & & \\ A_2 & A_1 & A_0 & \\ & A_2 & A_1 & \ddots \\ & & \ddots & \ddots\end{bmatrix}:$$
--   from level $0$ the rates are $B$ within level $0$ and $A_0$ to level $1$; from a level $n\ge 1$ they are $A_0$ to level $n+1$, $A_1$ within level $n$ and $A_2$ to level $n-1$; all other rates are $0$. The level $\ell(n)$ is the set of states $(n,i)$.
--
--   With $q_x$ the sojourn rate and expected sojourn times as in the file `Chain`:
--
--   - the **rate matrix** $R$ at level $n$ records the rate of sojourn in the states of $\ell(n+1)$ per unit of the local time of $\ell(n)$: $R_{ij}$ is $q_{(n,i)}$ times the expected time spent in $(n+1,j)$, starting from $(n,i)$, before the first return to $\ell(0)\cup\dots\cup\ell(n)$;
--   - the matrix $N$ at level $n\ge 1$ records the expected sojourn times in $\ell(n)$ before the first visit to $\ell(n-1)$: $N_{ij}$ is the expected time spent in $(n,j)$, starting from $(n,i)$, before the first visit to $\ell(n-1)$.
--
--   Both take values in $[0,+\infty]$, and so do the products $\sum_k M_{ik}M'_{kj}$, row-vector products $\sum_i v_iM_{ij}$ and powers $M^\nu$ of matrices with entries in $[0,+\infty]$ used with them.
--
--   Finally, a distribution $\pi$ on the states has **level independent of phase** if there are a probability vector $v$ on the phases and a probability density $\{\alpha_0,\alpha_1,\dots\}$ on the levels with
--   $$\pi_n=\alpha_n v,\qquad\text{i.e. } \pi_{(n,i)}=\alpha_n v_i\ \text{ for all } n,i .$$
--
--   **Formalization Note** Levels are counted from $0$. $R$ and $N$ are defined probabilistically, through the jump chain and mean holding times, never as solutions of the matrix equations of Chapters 6 and 8; $N$ at level $0$ is a meaningless value (ℕ subtraction) and is only used for $n\ge 1$. Products of nonnegative matrices are computed in $[0,+\infty]$ so that no summability hypothesis is needed for infinite phase sets.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 141, Eq. (6.19); p. 142, Theorem 6.4.1 (R and N); p. 297, proof of Theorem 15.1.1 (level independent of phase)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain

namespace MatrixAnalytic.ProductForm

noncomputable section

open scoped ENNReal

/-!
The homogeneous continuous-time QBD of §6.4 (p. 141, generator (6.19)) and §15.1 (p. 296) of
Latouche & Ramaswami: a Markov process on the states `(n, i)`, `n ≥ 0` the level and `i` the
phase, with block-tridiagonal generator. The phase set is an arbitrary type `ι` (it may be
infinite, as for the Jackson network of §15.2); levels are counted from `0`.

The rate matrix `R` (Theorem 6.4.1, p. 142) and the expected-sojourn matrix `N` are defined by
what they mean, through the jump chain and mean holding times of `Def_MatrixAnalytic_ProductForm_Chain`;
both take values in `ℝ≥0∞`, as do products and powers of nonnegative matrices (`matMulE`,
`matPowE`, `vecMulE`), so that every series is defined.
-/

variable {ι : Type*}

/-- The generator (6.19) of a homogeneous continuous-time QBD with blocks `B, A₀, A₁, A₂`:
from level `0` the rates are `B` within level `0` and `A₀` to level `1`; from a level `n ≥ 1`
they are `A₀` to level `n + 1`, `A₁` within level `n` and `A₂` to level `n − 1`; every other
entry is `0`. -/
def qbdQ (B A₀ A₁ A₂ : ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 = 0 then
      (if y.1 = 0 then B x.2 y.2 else if y.1 = 1 then A₀ x.2 y.2 else 0)
    else
      (if y.1 = x.1 + 1 then A₀ x.2 y.2
        else if y.1 = x.1 then A₁ x.2 y.2
        else if y.1 + 1 = x.1 then A₂ x.2 y.2
        else 0)

/-- The level `ℓ(n) = {(n, i) : i a phase}`. -/
def level (n : ℕ) : Set (ℕ × ι) := {x | x.1 = n}

/-- The set of levels `ℓ(0) ∪ ⋯ ∪ ℓ(n)`. -/
def levelsUpTo (n : ℕ) : Set (ℕ × ι) := {x | x.1 ≤ n}

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat (A : ι → ι → ℝ) : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Row vector times matrix in `ℝ≥0∞`: `(vM)_j = Σ_i v_i M_{ij}`. -/
def vecMulE (v : ι → ℝ≥0∞) (M : ι → ι → ℝ≥0∞) : ι → ℝ≥0∞ :=
  fun j => ∑' i, v i * M i j

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE (M M' : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE [DecidableEq ι] : ι → ι → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ℕ → ι → ι → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The rate matrix `R` at level `n` (Theorem 6.4.1, p. 142): "the rate of sojourn in the states
of `ℓ(n + 1)` per unit of the local time of `ℓ(n)`". Starting from `(n, i)`, whose sojourns have
mean `1/q_{(n,i)}`, `[rateR Q n]_{ij}` is `q_{(n,i)}` times the expected time spent in
`(n + 1, j)` before the first return to `ℓ(0) ∪ ⋯ ∪ ℓ(n)`. -/
def rateR [Countable ι] [DecidableEq ι] (Q : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (holdRate Q (n, i)) *
    sojournAvoid Q (levelsUpTo n) (n, i) (n + 1, j)

/-- The matrix `N` at level `n` (Theorem 6.4.1, p. 142): `[matNct Q n]_{ij}` is the expected
sojourn time in `(n, j)`, starting from `(n, i)`, before the first visit to `ℓ(n − 1)`.
Meant for `n ≥ 1`. -/
def matNct [Countable ι] [DecidableEq ι] (Q : ℕ × ι → ℕ × ι → ℝ) (n : ℕ) : ι → ι → ℝ≥0∞ :=
  fun i j => sojournAvoid Q (level (n - 1)) (n, i) (n, j)

/-- "The level is independent of the phase in steady state" (proof of Theorem 15.1.1, p. 297):
the stationary distribution factors as `π_n = α_n v`, i.e. `π_{(n,i)} = α_n v_i`, for some
probability vector `v` on the phases and some probability density `{α_0, α_1, …}` on the
levels. -/
def LevelPhaseIndependent (π : ℕ × ι → ℝ) : Prop :=
  ∃ (α : ℕ → ℝ) (v : ι → ℝ), (∀ n, 0 ≤ α n) ∧ HasSum α 1 ∧ (∀ i, 0 ≤ v i) ∧ HasSum v 1 ∧
    ∀ n i, π (n, i) = α n * v i

end

end MatrixAnalytic.ProductForm


