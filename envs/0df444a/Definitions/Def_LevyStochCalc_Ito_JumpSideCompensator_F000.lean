-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSideCompensator_F000
-- name    : LevyStochCalc_Ito_JumpSideCompensator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:42:55.180453+00:00
-- url     : https://prove2.me/theorems/26bb58e9-df2e-482a-a753-6ebe725574d6
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSideCompensator
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSideCompensator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A predictable integrand vanishing at the atoms

On a window of finite intensity the compensated integral of a predictable integrand is the
integral against the random measure minus the integral against the reference intensity, so an
integrand vanishing at every atom of the window has compensated integral minus its compensator.
The mark sets of finite intensity exhaust the mark space, the compensated integrals of the cut
integrands converge to the compensated integral of the integrand, and the compensators converge
to the compensator, so the identity survives at infinite activity.

## Main statements

* `stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` — the identity for an integrand
  vanishing at the atoms of every window built from the spanning sets of the mark measure. Both
  the vanishing and the integrability of the compensator are asked only on a set of sample
  points, and the conclusion holds there: an integrand that is square integrable against the
  intensity need not be integrable against it, so the compensator converges only where the
  hypothesis puts it.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSide

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Ito.IntegralLimit

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [IsProbabilityMeasure P] in
/-- The spanning sets of the mark measure eventually contain almost every mark. -/
theorem ae_eventually_mem_spanningSets :
    ∀ᵐ e ∂ν, ∀ᶠ j in atTop, e ∉ (spanningSets ν j)ᶜ := by
  filter_upwards with e
  have he : e ∈ ⋃ j, spanningSets ν j := by
    rw [iUnion_spanningSets ν]
    trivial
  obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.mp he
  filter_upwards [eventually_ge_atTop j₀] with j hj
  simpa using monotone_spanningSets ν hj hj₀
end LevyStochCalc.Ito.JumpSide


