-- Prove2me | Definitions.Def_SourceProof_6984d0dce12206fd688ba936
-- name    : SourceProof_6984d0dce12206fd688ba936
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:53:11.245898+00:00
-- url     : https://prove2.me/theorems/9e4af956-b11b-4341-a492-3ad217f31d0c
-- title:
--   LevyStochCalc source module: SourceProof_6984d0dce12206fd688ba936
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensator_F000
import Definitions.Def_LevyStochCalc_Poisson_Compensator_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_6984d0dce12206fd688ba936 {Y Z : Ω → ℝ} {X : ℕ → Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) (hZ : AEStronglyMeasurable Z P)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h1 : Tendsto (fun n => ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ∂P) atTop (𝓝 0)) :
    Y =ᵐ[P] Z := by
  have hsum : ∀ n : ℕ, ∫⁻ ω, ‖Y ω - Z ω‖ₑ ∂P
      ≤ (∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) + ∫⁻ ω, ‖X n ω - Z ω‖ₑ ∂P := by
    intro n
    have hpt : ∀ ω : Ω, ‖Y ω - Z ω‖ₑ ≤ ‖Y ω - X n ω‖ₑ + ‖X n ω - Z ω‖ₑ := by
      intro ω
      have hsplit : Y ω - Z ω = (Y ω - X n ω) + (X n ω - Z ω) := by ring
      rw [hsplit]
      exact enorm_add_le _ _
    exact le_trans (lintegral_mono hpt) (le_of_eq (lintegral_add_left'
      (measurable_enorm.comp_aemeasurable (hY.sub (hX n)).aemeasurable) _))
  have hzero : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ∂P = 0 := by
    refine le_antisymm ?_ bot_le
    exact ge_of_tendsto (by simpa using h1.add h2) (Eventually.of_forall hsum)
  have hae := (lintegral_eq_zero_iff'
    (measurable_enorm.comp_aemeasurable (hY.sub hZ).aemeasurable)).mp hzero
  filter_upwards [hae] with ω hω
  have hω0 : Y ω - Z ω = 0 := by
    simpa only [Function.comp_apply, Pi.sub_apply, Pi.zero_apply, enorm_eq_zero] using hω
  linarith
end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

end Pathwise

end LevyStochCalc.Poisson


