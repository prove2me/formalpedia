-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F002
-- name    : LevyStochCalc_Brownian_ItoSimpleIsometry_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:50:35.918797+00:00
-- url     : https://prove2.me/theorems/8e32f5d9-36fc-401a-8426-6eb10efe3907
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoSimpleIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoSimpleIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F001
import Definitions.Def_SourceProof_ea13c47aab5dc77f7cbb74e3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô isometry on simple predictable integrands

Expanding the square of the elementary integral into its diagonal and off-diagonal terms gives,
for an adapted simple predictable integrand `H` and a scalar Brownian motion `W`,
`E[(∫_0^T H dW) ^ 2] = ∑_i (t_{i+1} - t_i) · E[ξ_i ^ 2]`; combined with the energy of the
integrand this is the L²-isometry `E[(∫_0^T H dW) ^ 2] = ∫_0^T E[(H.eval s) ^ 2] ds`, stated
both for the lower integral and for the Bochner integral.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Outer Bochner integral of `(H.eval)²` over `Ω × [0,T]`** equals the
sum of `(t_{i+1} - t_i) · ∫ (ξ_i)² ∂P`. Bochner mirror of
`lintegral_eval_sq_outer`. -/
lemma integral_eval_sq_outer
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (H : SimplePredictable Ω T) :
    ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_inner : ∀ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 :=
    fun ω => _root_.Prove2MeSourceProof.h_ea13c47aab5dc77f7cbb74e3 H ω
  rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) from
    funext h_inner]
  -- Per-term integrability of `(t_{i+1} - t_i) · (ξ_i)²`.
  have h_int_term : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
      MeasureTheory.Integrable
        (fun ω => (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) P := by
    intro i _
    refine MeasureTheory.Integrable.const_mul ?_ _
    obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  rw [MeasureTheory.integral_finsetSum _ h_int_term]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul]
/-- **A2: L² isometry on simple integrands (Bochner integral form).**
For an adapted simple predictable integrand `H`,
`E[(simpleIntegral W H T)²] = ∫_0^T E[(H.eval s)²] ds`.

Combines `simpleIntegral_L2_isometry_brownian` (sum form) with
`integral_eval_sq_outer` (which expresses the same Σ in step-function
integral form). -/
theorem simpleIntegral_L2_isometry_brownian_integral_form
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_L2_isometry_brownian W ℱ hℱ H h_adapt]
  rw [integral_eval_sq_outer H]
end LevyStochCalc.Brownian.Ito


