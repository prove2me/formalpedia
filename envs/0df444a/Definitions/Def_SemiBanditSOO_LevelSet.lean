-- Prove2me | Definitions.Def_SemiBanditSOO_LevelSet
-- name    : SemiBanditSOO_LevelSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:00.951219+00:00
-- url     : https://prove2.me/theorems/7eeca3f3-8622-465a-82dd-54c51050b680
-- title:
--   Unions of intervals $\mathcal I_s$, level-set complexity, and the number of support points
-- statement:
--   For an integer $s\ge1$, $\mathcal I_s$ is the family of unions of at most $s$ intervals in $[0,1]$, including the empty set; intervals may be open, closed, half-open, or singletons.
--
--   A function $\phi$ on a subset $\mathrm{dom}(\phi)$ of $[0,1]$ has **level-set complexity at most $s$** if, for every $y\in\mathbb R$, there is $B\in\mathcal I_s$ such that its strict superlevel set satisfies
--   $$\{z\in\mathrm{dom}(\phi):\phi(z)>y\}=\mathrm{dom}(\phi)\cap B .$$
--   By convention every function has level-set complexity at most $\infty$. For example, monotone and unimodal functions have complexity at most $1$.
--
--   The **number of support points** $k\in\mathbb Z_{>0}\cup\{\infty\}$ of a distribution is the least cardinality of a finite set of full mass, and $\infty$ if no finite set has full mass.
--
--   These notions measure how the optimistic continuation values of the paper vary with the next revealed coordinate, and enter the regret bound through $S=\sum_i\min\{s_i,k_i\}$.
--
--   **Formalization Note.** An interval is an order-connected subset of $\mathbb R$; "at most $s$" intervals is $s$ possibly empty pieces. Complexities are elements of $\mathbb N_\infty$, and the predicate is trivially true at $\infty$. Functions are defined on the subtype $\mathrm{dom}$, and $\mathrm{dom}(\phi)\cap B$ is the preimage of $B$.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, §2.2, p.9 (ℐ_s, level-set complexity); Theorem 3.2, p.11 and Lemma 5.5, p.23 (support points)

import Mathlib

open MeasureTheory

namespace SemiBanditSOO

/-- **The families `ℐ_s`** (§2.2, p.9). Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic
Online Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, §2.2, p.9: for an integer
`s ≥ 1`, `ℐ_s` is the family of unions of at most `s` intervals in `[0, 1]`, including the empty
set; intervals may be open, closed, half-open, or singletons.

**Formalization Note.** An interval of `ℝ` is an order-connected set (`Set.OrdConnected`; this
includes `∅` and singletons). "At most `s`" intervals is encoded by `s` pieces, any of which may be
empty. -/
def IntervalUnions (s : ℕ) : Set (Set ℝ) :=
  {B | ∃ J : Fin s → Set ℝ, (∀ j, (J j).OrdConnected ∧ J j ⊆ Set.Icc 0 1) ∧ B = ⋃ j, J j}

/-- **Level-set complexity at most `s`** (§2.2, p.9). Harada, Kawase, Sumita, arXiv:2611.02739v1,
§2.2, p.9: a function `ϕ` on a subset `dom(ϕ)` of `[0, 1]` has level-set complexity at most `s` if,
for every `y ∈ ℝ`, there is `B ∈ ℐ_s` with `{z ∈ dom(ϕ) : ϕ(z) > y} = dom(ϕ) ∩ B`. By convention,
every function has level-set complexity at most `∞`.

**Formalization Note.** `s ∈ ℤ_{>0} ∪ {∞}` is an element of `ℕ∞`; for `s = ⊤` the predicate is
`True` (the paper's convention). The function is defined on the subtype `dom`, and
`dom(ϕ) ∩ B` is the preimage of `B` under the inclusion. The superlevel set is strict (`>`). -/
def LevelSetCpxLE {dom : Set ℝ} (s : ℕ∞) (ϕ : dom → ℝ) : Prop :=
  ∀ k : ℕ, s = (k : ℕ∞) → ∀ y : ℝ, ∃ B ∈ IntervalUnions k,
    {z : dom | y < ϕ z} = Subtype.val ⁻¹' B

/-- **The number of support points** `k ∈ ℤ_{>0} ∪ {∞}` of a distribution (Theorem 3.2, p.11; used
in Lemma 5.5, p.23, and its proof, "let `A` be the support of `P`").

**Formalization Note.** The least cardinality of a finite set of full mass, and `⊤` (`∞`) if no
finite set has full mass (e.g. a continuous distribution). For a discrete distribution this is the
number of atoms of positive mass. A probability measure has `supportCount ≥ 1`. -/
noncomputable def supportCount {α : Type*} [MeasurableSpace α] (μ : Measure α) : ℕ∞ :=
  ⨅ (A : Finset α) (_ : μ ((A : Set α)ᶜ) = 0), (A.card : ℕ∞)

end SemiBanditSOO


