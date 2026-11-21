-- Prove2me | Definitions.Def_SourceProof_c343f3fddeb9bb9bc3b8ffc2
-- name    : SourceProof_c343f3fddeb9bb9bc3b8ffc2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:04:44.121187+00:00
-- url     : https://prove2.me/theorems/d613c723-1725-4d2f-9969-8a5e874acb9a
-- title:
--   LevyStochCalc source module: SourceProof_c343f3fddeb9bb9bc3b8ffc2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.setIntegral_eval_sq_Icc_clamped` comes from the `LevyStochCalc.Brownian.ItoL2CompletionCompensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
import Definitions.Def_SourceProof_22c04691b34fae7b7b31973f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by
  have h_len_nn : ∀ i : Fin G.N,
      0 ≤ min (G.partition i.succ) t - min (G.partition i.castSucc) t :=
    fun i => sub_nonneg.mpr (min_le_min_right t
      (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))
  have h_eval_meas : Measurable (fun u => G.eval u ω) :=
    G.eval_jointly_measurable.comp
      (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
        (h_eval_meas.pow_const 2).aestronglyMeasurable]
  rw [show (fun u => ENNReal.ofReal ((G.eval u ω) ^ 2))
        = fun u => (‖G.eval u ω‖₊ : ℝ≥0∞) ^ 2 from funext (fun u => (h_norm_sq _).symm),
    _root_.Prove2MeSourceProof.h_22c04691b34fae7b7b31973f G ω,
    show (fun i : Fin G.N => ENNReal.ofReal (min (G.partition i.succ) t
          - min (G.partition i.castSucc) t) * (‖G.ξ i ω‖₊ : ℝ≥0∞) ^ 2)
        = fun i => ENNReal.ofReal ((min (G.partition i.succ) t
            - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2) from
      funext (fun i => by rw [h_norm_sq, ← ENNReal.ofReal_mul (h_len_nn i)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)),
    ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)))]
end LevyStochCalc.Brownian.Ito


