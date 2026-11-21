-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F001
-- name    : LevyStochCalc_Brownian_ItoSimpleIsometry_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:47:53.32975+00:00
-- url     : https://prove2.me/theorems/632ba9ad-f362-4bbe-a851-d26918c135a9
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoSimpleIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoSimpleIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F000
import Definitions.Def_SourceProof_a036b8f875718d55409e7876
import Definitions.Def_SourceProof_d116f889ac93596ce5014144

open private simpleIntegral_sq_bochner_eq from Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F000
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

/-- **Itô isometry on simple integrands.** The L²-norm of the simple integral
equals the L²-norm of the integrand against `dP ⊗ ds`. -/
lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (_hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [_root_.Prove2MeSourceProof.h_d116f889ac93596ce5014144 W ℱ hℱ H h_adapt]
  rw [_root_.Prove2MeSourceProof.h_a036b8f875718d55409e7876 H]
/-- **L² isometry on simple integrands (Bochner sum form).**
For an adapted simple predictable integrand
`H = ∑_i ξ_i · 1_{(t_i, t_{i+1}]}`,
`E[(∑_i ξ_i ΔB_i)²] = Σ_i (t_{i+1} - t_i) · E[ξ_i²]`.

Cross terms vanish by `simpleIntegral_offDiagonal` (which is the integral
form of the Brownian-increment martingale-difference property — see
`martingale_simpleIntegral_brownian`); the diagonal is computed in
`simpleIntegral_diagonal_bochner`. -/
theorem simpleIntegral_L2_isometry_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral W H T ω) ^ 2
      = (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq W ℱ hℱ H h_adapt
end LevyStochCalc.Brownian.Ito


