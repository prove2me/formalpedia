-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:25:02.80863+00:00
-- url     : https://prove2.me/theorems/01af51d1-de42-452d-987a-e735c9b0d7c1
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionQuadVar
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionQuadVar. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003
import Definitions.Def_SourceProof_7a12160ca4d56ce7d0871bc7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: isometry, right continuity and quadratic variation

The `L²`-isometry `∫⁻ ‖stochasticIntegralBrownian T‖₊² = ∫⁻ ∫⁻_{[0, T]} ‖H‖₊²`,
membership of the process in `L²(P)`, right `L²`-continuity of its time slices and
the resulting martingale property with respect to the right-continuation `ℱ₊` of
`ℱ`, and the compensator `∫_{[0, t]} (H ω u)² du` with the `ℱ`-martingale property
of the compensated square.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include h_meas in
omit [IsProbabilityMeasure P] in
/-- Additivity of the horizon integral: `[0,r] = [0,s] ⊎ (s,r]`. -/
lemma horizon_lintegral_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
        + ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
        MeasureTheory.lintegral_union measurableSet_Ioc
          (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [MeasureTheory.lintegral_congr hinner]
  exact MeasureTheory.lintegral_add_left'
    ((Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) s))
      (((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2)).aemeasurable) _
include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral `r ↦ ∫⁻∫⁻_{[0,r]}‖H‖²` at `s ≥ 0`. -/
lemma horizon_lintegral_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      (nhdsWithin s (Set.Ioi s))
      (nhds (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  have hz : Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    _root_.Prove2MeSourceProof.h_7a12160ca4d56ce7d0871bc7 (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
      (h_sq_int_global (s + 1) (by linarith)).ne
  have ht := (tendsto_const_nhds (x := ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s,
    (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizon_lintegral_add H h_meas hs (le_of_lt hr)).symm
end MasterSequence

end LevyStochCalc.Brownian.Ito


