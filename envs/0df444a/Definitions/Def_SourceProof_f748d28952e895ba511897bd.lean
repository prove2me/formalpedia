-- Prove2me | Definitions.Def_SourceProof_f748d28952e895ba511897bd
-- name    : SourceProof_f748d28952e895ba511897bd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:27.170639+00:00
-- url     : https://prove2.me/theorems/f8884235-2e38-408c-afe7-b94b0b4933d7
-- title:
--   LevyStochCalc source module: SourceProof_f748d28952e895ba511897bd
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_intermediate_brownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_07211334eb93145a1521a908
import Definitions.Def_SourceProof_57cbaf3ebcd16877e9db5e1f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H t ω) 2 P := by
  refine ⟨?_, ?_⟩
  · refine Measurable.aestronglyMeasurable ?_
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (H.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    rw [show (2 : ℝ≥0∞).toReal = 2 from by simp]
    have h_rewrite : (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2) := by
      funext ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
    rw [h_rewrite, _root_.Prove2MeSourceProof.h_07211334eb93145a1521a908 W ℱ hℱ H h_adapt ht_nn]
    -- bound `∫⁻∫⁻_{[0,t]} ≤ ∫⁻∫⁻_{[0,T]} < ⊤`.
    have h_fin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      rw [← LevyStochCalc.Brownian.Ito.simpleIntegral_isometry W ℱ hℱ hT H h_adapt]
      exact _root_.Prove2MeSourceProof.h_57cbaf3ebcd16877e9db5e1f W ℱ hℱ hT H h_adapt
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω => ?_)) h_fin
    exact lintegral_mono_set (Set.Icc_subset_Icc_right htT)
end LevyStochCalc.Brownian.Ito


