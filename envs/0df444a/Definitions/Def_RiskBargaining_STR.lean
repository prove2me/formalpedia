-- Prove2me | Definitions.Def_RiskBargaining_STR
-- name    : RiskBargaining_STR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:30:23.747891+00:00
-- url     : https://prove2.me/theorems/e74c5efc-8096-4d65-9503-b108810b09b4
-- title:
--   Axiom 3 (STR): strategy proofness
-- statement:
--   A rule $F$ satisfies **STR** if, for every admissible instance, every player $i$ and every $\ell\ge 1$, the values $u=F(R,M,\mathcal A)$ and $u'=F(R',M,\mathcal A')$ at the game associated by splitting $i$ into $\ell$ players satisfy
--   $$
--   u'_j=u_j\ \ (j\ne i),\qquad u'_{ik}=u_i/\ell\ \ (k=1,\dots,\ell).
--   $$
--   A player cannot gain by splitting into equal parts or by merging such parts.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Axiom 3 and equation (6), p.9

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_Admissible
import Definitions.Def_RiskBargaining_Instance_split

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Axiom 3 (STR).**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Axiom 3 and equation (6), p.9: with `u = F(R, M, 𝒜)` and `u′` the value of `F` at the game of
`Instance.split`, `u′_j = u_j` for `j ≠ i` and `u′_ik = u_i / ℓ` for `k = 1, …, ℓ`.

**Formalization Note.** Required at every admissible instance, every player and every `ℓ ≥ 1`. The split
of an admissible instance is admissible (`RiskBargaining.split_admissible_z`), so that is not a
hypothesis. -/
def STR (F : Rule μ p X) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
    I.Admissible → ∀ (i : ι) (ℓ : ℕ+),
      (∀ j : {j // j ≠ i}, F _ (I.split i ℓ) (Sum.inl j) = F ι I j) ∧
      (∀ k : Fin ℓ, F _ (I.split i ℓ) (Sum.inr k) = F ι I i / ((ℓ : ℕ) : ℝ))

end RiskBargaining


