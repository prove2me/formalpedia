-- Prove2me | Definitions.Def_PriceIgnorance_Pairwise_Instance
-- name    : PriceIgnorance_Pairwise_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:34.463481+00:00
-- url     : https://prove2.me/theorems/5cd17799-a2d8-4f9b-acc0-0fa145501018
-- title:
--   Marginals, couplings and the ambiguity sets $kI$ and $PI$ (Definition 2.1, footnote 3)
-- statement:
--   In the prophet inequality a gambler observes nonnegative values $V_1,\dots,V_n$, where $V_i$ has a known **marginal** law $D_i$. This definition fixes the instances.
--
--   1. A **value law** is a Borel probability measure on $\mathbb R$ giving no mass to $(-\infty,0)$ (values are nonnegative, p. 1).
--   2. Marginals $D_1,\dots,D_n$ are **non-degenerate** (footnote 3, p. 5) if each is a value law with finite mean and
--   $$0<\max_i \mathbb E_{V_i\sim D_i}[V_i]<\infty .$$
--   In particular $n\ge 1$. The paper excludes the other cases because the ratios below are then undefined.
--   3. A law on $\mathbb R$ has **finite support** if it is carried by a finite set. For finitely supported marginals, the **support grid** is the set of vectors $v$ with $D_i(\{v_i\})>0$ for every $i$.
--   4. A **coupling** of $D_1,\dots,D_n$ is a Borel probability measure $D$ on $\mathbb R^n$ whose $i$-th coordinate $V_i(v)=v_i$ has law $D_i$.
--   5. $kI(D_1,\dots,D_n)$ is the set of couplings under which the coordinates are **$k$-wise independent** (Definition 2.1): for every $S\subseteq[n]$ with $|S|\le k$ and all Borel sets $A_i$,
--   $$\mathbb P_D\Big[\bigwedge_{i\in S}V_i\in A_i\Big]=\prod_{i\in S}\mathbb P_D[V_i\in A_i].$$
--   6. $PI(D_1,\dots,D_n)=kI(D_1,\dots,D_n)$ with $k=2$, the **pairwise-independent** couplings.
--
--   These sets are the "ambiguity sets" over which a correlation-blind algorithm must perform well.
--
--   **Formalization Note** Indices are `Fin n` (0-based) and a value vector is `Fin n → ℝ`. $k$-wise independence is the published `LaconicBarrier.KWiseIndep` applied to the coordinate maps: every subfamily of at most $k$ coordinates is mutually independent (`iIndepFun`), which is Definition 2.1 for real random variables.
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 1; p. 3, Definition 2.1 and Notation; p. 5, footnote 3

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep

/-!
# Instances of the prophet inequality: marginals, couplings, `kI` and `PI`

Abdallah, Wajc, *Price of Ignorance in Pairwise-Independent Prophet Inequalities*, STOC 2027
submission (manuscript sha256 c79626fd…), p. 1 (§1), p. 3 (Definition 2.1, Notation),
p. 5 (footnote 3).

* A marginal `D_i` is a Borel probability measure on `ℝ` concentrated on `[0, ∞)` (values are
  nonnegative, p. 1).
* Non-degenerate marginals (footnote 3): every `E[V_i]` is finite and `max_i E[V_i] > 0`.
* `Couplings Dm`: Borel probability measures on `ℝⁿ = Fin n → ℝ` whose `i`-th coordinate law
  is `D_i`.
* `kI Dm k`: the couplings under which the coordinates are `k`-wise independent
  (Definition 2.1, via the published `LaconicBarrier.KWiseIndep`); `PI Dm = kI Dm 2`.
-/

namespace PriceIgnorance.Pairwise

open MeasureTheory ProbabilityTheory

/-- A law of one value: a probability measure on `ℝ` giving no mass to `(-∞, 0)`. -/
def IsValueLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0

/-- Non-degenerate marginals `D_1, …, D_n` (footnote 3, p. 5): laws of nonnegative values, each
with a finite mean, and `max_i E[V_i] > 0` (so in particular `n ≥ 1`). -/
def NonDegenerate {n : ℕ} (Dm : Fin n → Measure ℝ) : Prop :=
  (∀ i, IsValueLaw (Dm i)) ∧ (∀ i, Integrable id (Dm i)) ∧ ∃ i, 0 < ∫ x, x ∂(Dm i)

/-- A law on `ℝ` with finite support: it is carried by a finite set. -/
def HasFiniteSupport (μ : Measure ℝ) : Prop :=
  ∃ S : Finset ℝ, μ (↑S)ᶜ = 0

/-- The support grid `supp(D_1) × ⋯ × supp(D_n)` of finitely supported marginals: the value
vectors each of whose coordinates is an atom of its marginal. -/
def supportGrid {n : ℕ} (Dm : Fin n → Measure ℝ) : Set (Fin n → ℝ) :=
  {v | ∀ i, Dm i {v i} ≠ 0}

/-- The coordinate random variables `V_i(v) = v i` on `ℝⁿ`. -/
def coord {n : ℕ} : Fin n → (Fin n → ℝ) → ℝ :=
  fun i v => v i

/-- Joint distributions with marginals `D_1, …, D_n`: probability measures on `ℝⁿ` whose
`i`-th coordinate has law `D_i`. -/
def Couplings {n : ℕ} (Dm : Fin n → Measure ℝ) : Set (Measure (Fin n → ℝ)) :=
  {D | IsProbabilityMeasure D ∧ ∀ i, D.map (coord i) = Dm i}

/-- `kI(D_1, …, D_n)`: the joint distributions with marginals `D_1, …, D_n` under which the
coordinates are `k`-wise independent (Definition 2.1, p. 3). -/
def kI {n : ℕ} (Dm : Fin n → Measure ℝ) (k : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {D | D ∈ Couplings Dm ∧ LaconicBarrier.KWiseIndep D coord k}

/-- `PI(D_1, …, D_n) = kI(D_1, …, D_n)` with `k = 2`: the pairwise-independent joint
distributions with the given marginals. -/
def PI {n : ℕ} (Dm : Fin n → Measure ℝ) : Set (Measure (Fin n → ℝ)) :=
  kI Dm 2

end PriceIgnorance.Pairwise


