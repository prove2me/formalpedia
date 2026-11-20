-- Prove2me | Definitions.Def_SourceProof_d1a830962090e7daf9e48a75
-- name    : SourceProof_d1a830962090e7daf9e48a75
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:11:52.981236+00:00
-- url     : https://prove2.me/theorems/c5cca2c8-92e5-48c4-9275-605ae7fb1a07
-- title:
--   LevyStochCalc source module: SourceProof_d1a830962090e7daf9e48a75
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.tendsto_lintegral_enorm_of_eLpNorm` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F001

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


theorem _root_.Prove2MeSourceProof.h_d1a830962090e7daf9e48a75 {Y : Ω → ℝ} {X S : ℕ → Ω → ℝ}
    (hY : AEStronglyMeasurable Y P) (hS : ∀ n, AEStronglyMeasurable (S n) P)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (h1 : Tendsto (fun n => eLpNorm (fun ω => S n ω - Y ω) 2 P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => (∫⁻ ω, ‖S n ω - X n ω‖ₑ ^ 2 ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using h1.add h2) (fun n => bot_le) fun n => ?_
  have hpt : ∀ ω : Ω, ‖Y ω - X n ω‖ₑ ≤ ‖Y ω - S n ω‖ₑ + ‖S n ω - X n ω‖ₑ := by
    intro ω
    have hsplit : Y ω - X n ω = (Y ω - S n ω) + (S n ω - X n ω) := by ring
    rw [hsplit]
    exact enorm_add_le _ _
  have hsum : ∫⁻ ω, ‖Y ω - X n ω‖ₑ ∂P
      ≤ (∫⁻ ω, ‖Y ω - S n ω‖ₑ ∂P) + ∫⁻ ω, ‖S n ω - X n ω‖ₑ ∂P :=
    le_trans (lintegral_mono hpt) (le_of_eq (lintegral_add_left'
      (measurable_enorm.comp_aemeasurable (hY.sub (hS n)).aemeasurable) _))
  refine hsum.trans (add_le_add ?_ ?_)
  · refine (LevyStochCalc.Poisson.lintegral_enorm_le_eLpNorm_two (hY.sub (hS n))).trans (le_of_eq ?_)
    exact eLpNorm_sub_comm Y (S n) 2 P
  · exact (LevyStochCalc.Poisson.lintegral_enorm_le_eLpNorm_two ((hS n).sub (hX n))).trans
      (le_of_eq (LevyStochCalc.Poisson.eLpNorm_two_eq_rpow _))
end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

end Pathwise

end LevyStochCalc.Poisson


