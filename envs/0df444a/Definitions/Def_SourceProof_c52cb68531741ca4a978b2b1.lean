-- Prove2me | Definitions.Def_SourceProof_c52cb68531741ca4a978b2b1
-- name    : SourceProof_c52cb68531741ca4a978b2b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:13:47.306312+00:00
-- url     : https://prove2.me/theorems/52f3936f-81dd-4735-a184-ebd316e6f015
-- title:
--   LevyStochCalc source module: SourceProof_c52cb68531741ca4a978b2b1
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` comes from the `LevyStochCalc.Ito.ItoLevyMixedBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_BigJumpPathBridge_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaContinuity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaTaylorBounds_F000
import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
import Definitions.Def_LevyStochCalc_Ito_SubsequenceBookkeeping_F000
import Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_c52cb68531741ca4a978b2b1 {n d : ℕ}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {coeffs : JumpDiffusionCoeffs n d E}
    {Xp Y : ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ i, ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hγ : ∀ i, MarkedProgressivelyMeasurable ℱ (SmallJump.pathJumpCoeff coeffs Xp i)) :
    MarkedProgressivelyMeasurable ℱ fun ω s e =>
      ((s, Y s ω, coeffs.γ s (Xp s ω) e) : ℝ × (Fin n → ℝ) × (Fin n → ℝ)) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have heq : (fun p : Ω × ℝ × E => (Set.Iic t).indicator
        (fun s => ((s, Y s p.1, coeffs.γ s (Xp s p.1) p.2.2) :
          ℝ × (Fin n → ℝ) × (Fin n → ℝ))) p.2.1)
      = fun p : Ω × ℝ × E => ((Set.Iic t).indicator (fun s => s) p.2.1,
          fun i => (Set.Iic t).indicator (fun s => Y s p.1 i) p.2.1,
          fun i => (Set.Iic t).indicator (fun s => coeffs.γ s (Xp s p.1) p.2.2 i) p.2.1) := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp]
      rfl
  rw [heq]
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_id.indicator measurableSet_Iic).comp measurable_snd.fst
  · refine measurable_pi_lambda _ fun i => ?_
    exact ((hY i t).measurable).comp (measurable_fst.prodMk measurable_snd.fst)
  · refine measurable_pi_lambda _ fun i => ?_
    exact (hγ i t).measurable
end Progressive

end LevyStochCalc.Ito.JumpFormula


