-- Prove2me | Definitions.Def_RiskBargaining_Instance_U
-- name    : RiskBargaining_Instance_U
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:26:36.944625+00:00
-- url     : https://prove2.me/theorems/1dc6e80b-8fa1-4b9e-8637-918eedee7f9f
-- title:
--   The set $\mathcal U(R,M,\mathcal A)$ of feasible acceptability allocations, (5)
-- statement:
--   For an instance $(R,M,\mathcal A)$, the set of **feasible acceptability allocations** is
--   $$
--   \mathcal U(R,M,\mathcal A)=\Big\{u\in\mathbb R^n \;\Big|\; \exists x\in\mathcal X\ \exists L:\ \sum_{i=1}^n L_i\overset{a.s.}{=}M_x,\ L_i\in L^p,\ \mathcal A_i(R_i)\le u_i\le\mathcal A_i(L_i),\ i\in N\Big\}.
--   $$
--   A bargaining solution selects one point of this set.
--
--   **Formalization Note** Equality in `Lp` is equality almost surely. The upper condition is an inequality, as printed.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, equation (5), p.8

import Mathlib
import Definitions.Def_RiskBargaining_Instance_v

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The set of feasible acceptability allocations** `𝒰(R, M, 𝒜)`.
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, equation (5), p.8.

`u ∈ 𝒰` when some decision `x` and some allocation `L` with `∑ i, L i = M x` satisfy
`v i ≤ u i ≤ A i (L i)` for every player.

**Formalization Note.** Equality in `Lp` is equality almost surely, as in (5). The upper condition is an
inequality, as printed. -/
def Instance.U [Fintype ι] (I : Instance μ p X ι) : Set (ι → ℝ) :=
  {u | ∃ x : X, ∃ L : ι → Lp ℝ p μ, ∑ i, L i = I.M x ∧ ∀ i, I.v i ≤ u i ∧ u i ≤ I.A i (L i)}

end RiskBargaining


