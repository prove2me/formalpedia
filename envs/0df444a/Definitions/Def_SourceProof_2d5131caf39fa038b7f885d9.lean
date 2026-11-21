-- Prove2me | Definitions.Def_SourceProof_2d5131caf39fa038b7f885d9
-- name    : SourceProof_2d5131caf39fa038b7f885d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:39:49.454727+00:00
-- url     : https://prove2.me/theorems/5c49df0d-e862-46bf-91f4-1b324012ede3
-- title:
--   LevyStochCalc source module: SourceProof_2d5131caf39fa038b7f885d9
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.setIntegral_increment_sq_eq` comes from the `LevyStochCalc.Poisson.CompensatedQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F000
import Definitions.Def_SourceProof_6839e78f61d86c5ab0f11397
import Definitions.Def_SourceProof_96968c8d5a5450421d19e3bc

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_2d5131caf39fa038b7f885d9 (hG : G.Adapted ℱ) {s t : ℝ} (hst : s ≤ t) {B : Set Ω}
    (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, (G.integral N t ω - G.integral N s ω) ^ 2 ∂P
      = ∫ ω in B, (G.compensator t ω - G.compensator s ω) ∂P := by
  have hBm : MeasurableSet B := ℱ.le s B hB
  set w : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hwdef
  have hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C := ⟨1, fun ω => LevyStochCalc.Poisson.Compensated.MarkStep.abs_indicator_one_le B ω⟩
  have hwm : Measurable w := measurable_const.indicator hBm
  have hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w :=
    stronglyMeasurable_const.indicator hB
  have hind : ∀ f : Ω → ℝ, ∫ ω, (w ω) ^ 2 * f ω ∂P = ∫ ω in B, f ω ∂P := by
    intro f
    rw [← integral_indicator hBm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ B
    · simp [hwdef, Set.indicator_of_mem hω]
    · simp [hwdef, Set.indicator_of_notMem hω]
  have hsq : ∀ f : Ω → ℝ, ∫ ω, (w ω * f ω) ^ 2 ∂P = ∫ ω in B, (f ω) ^ 2 ∂P := by
    intro f
    rw [← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  rcases eq_or_lt_of_le hst with rfl | hlt
  · simp
  rcases le_or_gt t 0 with ht | ht
  · have h1 : ∀ ω, G.integral N t ω - G.integral N s ω = 0 := fun ω => by
        rw [G.integral_eq_zero_of_nonpos N ht, G.integral_eq_zero_of_nonpos N (hst.trans ht),
        sub_zero]
    have h2 : ∀ ω, G.compensator t ω - G.compensator s ω = 0 := fun ω => by
      rw [G.compensator_of_nonpos ht, G.compensator_of_nonpos (hst.trans ht), sub_zero]
    simp only [h1, h2]
    simp
  rcases le_or_gt s 0 with hs | hs
  · have h1 : ∀ ω, G.integral N t ω - G.integral N s ω = G.integral N t ω := fun ω => by
      rw [G.integral_eq_zero_of_nonpos N hs, sub_zero]
    have h2 : ∀ ω, G.compensator t ω - G.compensator s ω = G.compensator t ω := fun ω => by
      rw [G.compensator_of_nonpos hs, sub_zero]
    simp only [h1, h2]
    rw [← hsq, (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_96968c8d5a5450421d19e3bc p2mMethodArg0 p2mMethodArg1 G) N hℱ hw hwm hG ht.le
      (hwa.mono (ℱ.mono hs)), ← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [G.integral_integral_eval_sq_swap measure_Icc_lt_top.ne]
    rfl
  · rw [← hsq, (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_6839e78f61d86c5ab0f11397 p2mMethodArg0 p2mMethodArg1 G) N hℱ hw hwm hs hlt hG hwa, ← hind]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [G.integral_integral_eval_sq_swap measure_Ioc_lt_top.ne,
      G.compensator_sub hs.le hlt.le]
end MarkStep

end LevyStochCalc.Poisson.Compensated


