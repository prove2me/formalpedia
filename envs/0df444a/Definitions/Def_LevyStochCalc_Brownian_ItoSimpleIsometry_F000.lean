-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F000
-- name    : LevyStochCalc_Brownian_ItoSimpleIsometry_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:28:34.947223+00:00
-- url     : https://prove2.me/theorems/128cc167-420a-4fff-8986-41537bed8e55
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoSimpleIsometry
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoSimpleIsometry. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_SourceProof_ade4537669e1061d312e165f
import Definitions.Def_SourceProof_bfd78118d51ae0bbee2cf99f
import Definitions.Def_SourceProof_f7a893cd187625d17fc60e78

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

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction for Brownian.** -/
private lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2 ∂P
      = ∑ i : Fin H.N,
        (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2
      = ∑ i : Fin H.N, ∑ j : Fin H.N,
          (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
          (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
            (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω)) *
            (H.ξ j ω * (W.W (H.partition j.succ) ω
                      - W.W (H.partition j.castSucc) ω)) from funext h_expand]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => _root_.Prove2MeSourceProof.h_ade4537669e1061d312e165f W H i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => _root_.Prove2MeSourceProof.h_ade4537669e1061d312e165f W H i j)]
  rw [Finset.sum_eq_single i]
  · -- j = i: diagonal Bochner
    have h_part_nn : 0 ≤ H.partition i.castSucc := by
      have : H.partition 0 ≤ H.partition i.castSucc :=
        H.partition_strictMono.monotone (Fin.zero_le _)
      rw [H.partition_zero] at this; exact this
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)))
          = fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2 from by
      funext ω; ring]
    exact _root_.Prove2MeSourceProof.h_bfd78118d51ae0bbee2cf99f W ℱ hℱ H i h_part_nn (h_adapt i)
  · -- j ≠ i: offDiagonal (with symmetry)
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                         (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)))
            = fun ω => (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) from by
        funext ω; ring]
      exact _root_.Prove2MeSourceProof.h_f7a893cd187625d17fc60e78 W ℱ hℱ H h_lt (h_adapt j) (h_adapt i)
    · exact _root_.Prove2MeSourceProof.h_f7a893cd187625d17fc60e78 W ℱ hℱ H h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not
end LevyStochCalc.Brownian.Ito


