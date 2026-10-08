-- Prove2me | Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
-- name    : KingmanSubadditive_PositiveMatrices_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:56.402919+00:00
-- url     : https://prove2.me/theorems/2b6713d6-f220-4052-8c52-7bc54f98c6f2
-- title:
--   §2.2 — random matrix products X_n = Y₁⋯Y_n, z_st, x_st = −log z_st, the ℓ₁-norm, stationarity, the hypotheses of Theorem 5, and S₁, S₂, g_t
-- statement:
--   This file fixes the objects of Kingman's §2.2 (products of random matrices) on a probability space $(\Omega,\mathcal F,P)$. Let $k\ge 1$ and let $Y_1,Y_2,\dots$ be random $k\times k$ real matrices.
--
--   1. **Ordered products.** For $s<t$, $Y_{s+1}Y_{s+2}\cdots Y_t$ is the product taken left to right in increasing index order. In particular
--   $$X_n=Y_1Y_2\cdots Y_n\quad(2.2.1),\qquad X_n'=Y_2Y_3\cdots Y_{n+1},$$
--   with $X_0$ the identity (empty product).
--   2. **The diagonal process.** $z_{st}=[Y_{s+1}Y_{s+2}\cdots Y_t]_{11}$ and $x_{st}=-\log z_{st}$ for $s<t$; $[\cdot]_{ij}$ denotes the $(i,j)$th entry.
--   3. **The $\ell_1$-norm** $\|A\|=\max_i\sum_j|[A]_{ij}|$ (maximum absolute row sum).
--   4. **Stationarity.** $(Y_n)_{n\ge1}$ is stationary if the joint law of $(Y_{n+1})_{n\ge1}$ on the sequence space (product $\sigma$-algebra) equals that of $(Y_n)_{n\ge1}$.
--   5. **Hypotheses of Theorem 5.** Each $Y_n$ is measurable, every entry of every $Y_n$ is strictly positive, every $\log [Y_n]_{ij}$ has finite expectation, and $(Y_n)$ is stationary.
--   6. **The conditions of §1.1** for a family $(x_{st})_{s<t}$: S₁ is $x_{su}\le x_{st}+x_{tu}$ for $s<t<u$; S₂ says the joint distributions of $(x_{s+1,t+1})$ are those of $(x_{st})$; $g_t=E(x_{0t})$.
--
--   These are the objects in which Kingman deduces the Furstenberg–Kesten theorem from his subadditive ergodic theorem.
--
--   **Formalization Note.** Matrices are `Matrix (Fin k) (Fin k) ℝ` and the paper's index $1$ is `0 : Fin k` (hence `NeZero k`). The sequence is indexed from $1$; `Y 0` is never read. Positivity is required at every outcome. S₁ and S₂ use the group's frozen shared §1.1 process module; $g_t$ is defined locally.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 883–884 (§1.1, S₁, S₂, (1.1.2)), pp. 891–892 (§2.2, (2.2.1), Theorem 5 and its proof)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.PositiveMatrices

open MeasureTheory

/-- The ordered block product `Y_{s+1} Y_{s+2} ⋯ Y_t` of §2.2 (Kingman, *Subadditive ergodic
theory*, Ann. Probab. 1(6):883–899 (1973), p. 891), multiplied **left to right** in
increasing index order.

**Formalization Note.** `List.range' (s+1) (t-s)` is the list `[s+1, …, t]`; for `t ≤ s` it is
empty and the product is the identity matrix (a value never used: every statement uses
`s < t`, or `X₀ = 1`). The sequence is indexed from `1` as in the paper; `Y 0` is never read. -/
def blockProd {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (s t : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  ((List.range' (s + 1) (t - s)).map (fun r => Y r ω)).prod

/-- `X_n = Y₁ Y₂ ⋯ Y_n`, (2.2.1), p. 891. `X 0 = 1` (empty product). -/
def X {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  blockProd Y 0 n ω

/-- `X_n′ = Y₂ Y₃ ⋯ Y_{n+1}`, proof of Theorem 5, p. 892. -/
def X' {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  blockProd Y 1 (n + 1) ω

/-- `z_st = [Y_{s+1} Y_{s+2} ⋯ Y_t]₁₁`, proof of Theorem 5, p. 891. The paper's index `1`
is `0 : Fin k`. -/
def z {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (s t : ℕ) (ω : Ω) :
    ℝ :=
  blockProd Y s t ω 0 0

/-- `x_st = −log z_st`, proof of Theorem 5, p. 891 (meaningful when `z_st > 0`, which holds
for `s < t` under the positivity hypothesis of Theorem 5). -/
noncomputable def x {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (s t : ℕ) (ω : Ω) : ℝ :=
  -Real.log (z Y s t ω)

/-- The ℓ₁-norm of p. 892, `‖A‖ = max_i Σ_j |[A]_ij|` (maximum row sum of absolute values).
Written out explicitly: the constant `E log ‖Y₁‖` depends on the norm. Needs `k ≥ 1`. -/
noncomputable def rowSumNorm {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, |A i j|)

/-- **Stationarity** of the sequence `(Y_n)_{n ≥ 1}` (Theorem 5, p. 891): the joint law of the
shifted sequence `(Y_{n+1})_{n ≥ 1}` equals the joint law of `(Y_n)_{n ≥ 1}`, both as measures
on the sequence space `ℕ → (Fin k → Fin k → ℝ)` with its product σ-algebra. This is joint-law
stationarity, strictly stronger than "identically distributed". -/
def IsStationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Measure.map (fun ω (n : ℕ) (i j : Fin k) => Y (n + 2) ω i j) P =
    Measure.map (fun ω (n : ℕ) (i j : Fin k) => Y (n + 1) ω i j) P

/-- The hypotheses of Theorem 5 (p. 891) on random `k × k` matrices `Y₁, Y₂, …`:
1. each `Y_n` (`n ≥ 1`) is a random matrix, i.e. measurable;
2. the elements of every `Y_n` are strictly positive (for every outcome);
3. their logarithms have finite expectations: `log [Y_n]_ij` is integrable for every `n ≥ 1`
   and every `i, j`;
4. the sequence `(Y_n)` is stationary (`IsStationary`). -/
def Hypotheses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → Measurable (fun ω (i j : Fin k) => Y n ω i j)) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ ω i j, 0 < Y n ω i j) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ i j, Integrable (fun ω => Real.log (Y n ω i j)) P) ∧
  IsStationary P Y

/-! ### The subadditive-process conditions of §1.1 (pp. 883–884), for a family `x s t`. -/

/-- The shifted KingmanSubadditive.Ergodic.path `(x_{s+1,t+1})`. -/
def shiftedPath {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) : KingmanSubadditive.Ergodic.Interval → ℝ :=
  fun p => x (p.1.1 + 1) (p.1.2 + 1) ω

/-- `g_t = E(x_{0t})`, (1.1.2), p. 883. -/
noncomputable def g {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ)
    (t : ℕ) : ℝ :=
  ∫ ω, x 0 t ω ∂P

end KingmanSubadditive.PositiveMatrices


