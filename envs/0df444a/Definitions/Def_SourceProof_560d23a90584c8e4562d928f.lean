-- Prove2me | Definitions.Def_SourceProof_560d23a90584c8e4562d928f
-- name    : SourceProof_560d23a90584c8e4562d928f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:24:53.85117+00:00
-- url     : https://prove2.me/theorems/f682ed6f-f1e5-449a-b433-f7bd67a3b9a6
-- title:
--   LevyStochCalc source module: SourceProof_560d23a90584c8e4562d928f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.compensatorH_memLp_prod` comes from the `LevyStochCalc.Brownian.ItoL2CompletionQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F003

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

include h_meas h_sq_int_global in
omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_560d23a90584c8e4562d928f {t : ℝ} (ht : 0 < t) :
    MeasureTheory.MemLp (fun p : Ω × ℝ => H p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤),
    show (2 : ℝ≥0∞).toReal = 2 from by simp]
  have hbridge : ∫⁻ p : Ω × ℝ, (‖H p.1 p.2‖ₑ) ^ (2 : ℝ)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [MeasureTheory.lintegral_prod _
      ((((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2).aemeasurable.congr
        (Filter.Eventually.of_forall (fun p => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl)))]
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
  rw [hbridge]; exact h_sq_int_global t ht
end MasterSequence

end LevyStochCalc.Brownian.Ito


