-- Prove2me | Definitions.Def_MatrixAnalytic_FirstPassage_Passage
-- name    : MatrixAnalytic_FirstPassage_Passage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:47.656993+00:00
-- url     : https://prove2.me/theorems/31b88b0a-63de-448b-999a-4846d13f22d5
-- title:
--   First passage times t_{n→k}, probabilities Γ_{n→k}, and the bisection quantities s_i^{(n)}, G_i^{(n)}, Γ_i^{(n)} as taboo path sums; the matrices C_n
-- statement:
--   Let $P$ be a transition matrix on the level–phase states $(n,i)$, with $\tau(k)=\inf\{j>0 : X_j\in\ell(k)\}$ the first passage time to level $\ell(k)$. All the following are defined through the hitting quantities of the chain (sums over taboo trajectories), never through the equations of Chapter 11.
--
--   1. $t_{n\to k}$ is the vector with entries $\mathrm E[\tau(k)\mid X_0=(n,i)]$, the expected first passage times from the states of $\ell(n)$ to $\ell(k)$; by convention $t_{n\to n}=0$.
--   2. $\Gamma_{n\to k}$ is the matrix with entries $\mathrm P[\tau(k)<\infty,\ X_{\tau(k)}=(k,j)\mid X_0=(n,i)]$, the first passage probabilities from $\ell(n)$ to $\ell(k)$ indexed by initial and arrival phase; by convention $\Gamma_{n\to n}=I$.
--   3. With $\theta^{(n)}=\min(\tau(0),\tau(n+1))$ and $1\le i\le n$: $s_i^{(n)}$ has entries $\mathrm E[\theta^{(n)}\mid X_0=(i,p)]$; $G_i^{(n)}$ has entries $\mathrm P[\theta^{(n)}=\tau(0)<\tau(n+1),\ X_{\tau(0)}=(0,q)\mid X_0=(i,p)]$; $\Gamma_i^{(n)}$ has entries $\mathrm P[\theta^{(n)}=\tau(n+1)<\tau(0),\ X_{\tau(n+1)}=(n+1,q)\mid X_0=(i,p)]$.
--   4. The matrices of Lemma 11.2.2: $C_0=P_{00}$ and $C_n=A_1+A_2\Gamma_{n-1\to n}$ for $n\ge1$.
--   5. The matrices of Lemma 10.1.1, Eq. (10.3): $C_0=P_{00}$ and $C_i=A_1+A_2(I-C_{i-1})^{-1}A_0$ for $i\ge1$ (used only by the corrected variant of Lemma 11.2.2).
--
--   **Formalization Note** Expectations and probabilities are in `ℝ≥0∞` (tail sums and hitting distributions of the Chain definitions). `toRealMat` and `toRealVec` read them as real matrices and vectors; the theorems that use them state the finiteness that makes this reading exact. In $C_n$, $\Gamma_{n-1\to n}$ enters as a real matrix; in (10.3) the inverse is Mathlib's matrix inverse. `sBis`, `GBis`, `GamBis` take $n$ first and the starting level $i$ second.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 242 (t_{n→k}, Γ_{n→k}), p. 243 (C_n, Lemma 11.2.2), p. 245 (s_i^{(n)}, G_i^{(n)}, Γ_i^{(n)}), p. 223 (Eq. (10.3))

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD

namespace MatrixAnalytic.FirstPassage

noncomputable section

open scoped ENNReal

/-!
The first-passage quantities of Chapter 11 of Latouche & Ramaswami for a chain with transition
matrix `P` on the level–phase states `ℕ × ι` (in the chapter, `P` is the finite QBD (10.2)).
All are taboo path sums (`Def_MatrixAnalytic_FirstPassage_Chain`), never solutions of the
chapter's equations:

* `tPass P n k` = `t_{n→k} = E[τ(k) | X₀ ∈ ℓ(n)]` and `GammaPass P n k` =
  `Γ_{n→k} = P[X_{τ(k)} | X₀ ∈ ℓ(n)]` (p. 242), with the convention `t_{n→n} = 0`,
  `Γ_{n→n} = I`;
* `sBis P n i`, `GBis P n i`, `GamBis P n i` = `s_i^{(n)}`, `G_i^{(n)}`, `Γ_i^{(n)}` (p. 245),
  where `θ^{(n)} = min(τ(0), τ(n + 1))`;
* `matC` = the matrices `C_n` of Lemma 11.2.2 (p. 243) in the form `C₀ = P₀₀`,
  `C_n = A₁ + A₂Γ_{n−1→n}`, and `matCrec` = the recursion (10.3) of Lemma 10.1.1 (p. 223).

Here `τ(k) = inf{j > 0 : X_j ∈ ℓ(k)}` (p. 240).
-/

variable {ι : Type*}

/-- `t_{n→k}` (p. 242): entry `i` is the expected first passage time `E[τ(k) | X₀ = (n, i)]` to
the level `ℓ(k)`, with the convention `t_{n→n} = 0`. -/
def tPass (P : ℕ × ι → ℕ × ι → ℝ) (n k : ℕ) : ι → ℝ≥0∞ :=
  fun i => if n = k then 0 else expHitTime P (level k) (n, i)

/-- `Γ_{n→k}` (p. 242): entry `(i, j)` is the probability, starting from `(n, i)`, that the
level `ℓ(k)` is reached and first entered at `(k, j)`; with the convention `Γ_{n→n} = I`. -/
def GammaPass [DecidableEq ι] (P : ℕ × ι → ℕ × ι → ℝ) (n k : ℕ) : Matrix ι ι ℝ≥0∞ :=
  fun i j => if n = k then (if i = j then 1 else 0) else hitDist P (level k) (n, i) (k, j)

/-- `s_i^{(n)} = E[θ^{(n)} | X₀ ∈ ℓ(i)]` (p. 245): entry `p` is the expected time, starting
from `(i, p)`, until the first visit (after time `0`) to `ℓ(0) ∪ ℓ(n + 1)`. Meant for
`1 ≤ i ≤ n`. -/
def sBis (P : ℕ × ι → ℕ × ι → ℝ) (n i : ℕ) : ι → ℝ≥0∞ :=
  fun p => expHitTime P (level 0 ∪ level (n + 1)) (i, p)

/-- `G_i^{(n)} = P[θ^{(n)} = τ(0) < τ(n + 1) & X_{τ(0)} | X₀ ∈ ℓ(i)]` (p. 245): entry `(p, q)` is
the probability, starting from `(i, p)`, that `ℓ(0) ∪ ℓ(n + 1)` is reached and first entered at
`(0, q)`. Meant for `1 ≤ i ≤ n`. -/
def GBis (P : ℕ × ι → ℕ × ι → ℝ) (n i : ℕ) : Matrix ι ι ℝ≥0∞ :=
  fun p q => hitDist P (level 0 ∪ level (n + 1)) (i, p) (0, q)

/-- `Γ_i^{(n)} = P[θ^{(n)} = τ(n + 1) < τ(0) & X_{τ(n+1)} | X₀ ∈ ℓ(i)]` (p. 245): entry `(p, q)`
is the probability, starting from `(i, p)`, that `ℓ(0) ∪ ℓ(n + 1)` is reached and first entered
at `(n + 1, q)`. Meant for `1 ≤ i ≤ n`. -/
def GamBis (P : ℕ × ι → ℕ × ι → ℝ) (n i : ℕ) : Matrix ι ι ℝ≥0∞ :=
  fun p q => hitDist P (level 0 ∪ level (n + 1)) (i, p) (n + 1, q)

/-- A matrix with entries in `ℝ≥0∞` read as a real matrix (each entry through `toReal`). -/
def toRealMat (A : Matrix ι ι ℝ≥0∞) : Matrix ι ι ℝ := A.map ENNReal.toReal

/-- A vector with entries in `ℝ≥0∞` read as a real vector (each entry through `toReal`). -/
def toRealVec (v : ι → ℝ≥0∞) : ι → ℝ := fun i => (v i).toReal

/-- The matrices `C_n` of Lemma 11.2.2 (p. 243) in the form the lemma's proof uses:
`C₀ = P₀₀` and `C_n = A₁ + A₂Γ_{n−1→n}` for `n ≥ 1`, with `Γ_{n−1→n}` the first passage
probability matrix of the chain `P`. -/
def matC [Fintype ι] [DecidableEq ι] (P : ℕ × ι → ℕ × ι → ℝ) (P₀₀ A₁ A₂ : Matrix ι ι ℝ)
    (n : ℕ) : Matrix ι ι ℝ :=
  if n = 0 then P₀₀ else A₁ + A₂ * toRealMat (GammaPass P (n - 1) n)

/-- The matrices `C_i` of Lemma 10.1.1 (p. 223, Eq. (10.3)) for `0 ≤ i ≤ M − 1`:
`C₀ = P₀₀`, `C_i = A₁ + A₂(I − C_{i−1})⁻¹A₀` (with Mathlib's matrix inverse). -/
def matCrec [Fintype ι] [DecidableEq ι] (P₀₀ A₀ A₁ A₂ : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => P₀₀
  | n + 1 => A₁ + A₂ * (1 - matCrec P₀₀ A₀ A₁ A₂ n)⁻¹ * A₀

end

end MatrixAnalytic.FirstPassage


