-- Prove2me | Definitions.Def_SourceProof_0d5475ecda5b11387d030812
-- name    : SourceProof_0d5475ecda5b11387d030812
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:09:22.459611+00:00
-- url     : https://prove2.me/theorems/a8a28eaf-de5a-40c7-8951-f80c4245bb42
-- title:
--   LevyStochCalc source module: SourceProof_0d5475ecda5b11387d030812
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.brownian_increment_sq_integrable` comes from the `LevyStochCalc.Brownian.ItoSimpleMoments` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second moments of the terms of the elementary Brownian integral

For an adapted simple predictable integrand the diagonal term satisfies
`E[(ξ_i · ΔW_i) ^ 2] = (t_{i+1} - t_i) · E[ξ_i ^ 2]`, where
`ΔW_i = W_{t_{i+1}} - W_{t_i}`, since `ΔW_i` is independent of `ℱ_{t_i}` and centred Gaussian
with variance `t_{i+1} - t_i`, while for `i < j` the off-diagonal term vanishes,
`E[(ξ_i · ΔW_i) · (ξ_j · ΔW_j)] = 0`. Both rest on the integrability of the squared increments
and of the cross products.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_0d5475ecda5b11387d030812
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (h_s_nn : 0 ≤ s) (h_st : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω)^2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  have h_law := W.increment_gaussian h_s_nn h_st
  -- Convert to integrability on the pushforward measure (gaussianReal).
  have h_x_sq_meas : Measurable (fun x : ℝ => x^2) :=
    measurable_id.pow_const 2
  rw [show (fun ω => (W.W t ω - W.W s ω)^2)
        = (fun x : ℝ => x^2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P)
      (f := fun ω => W.W t ω - W.W s ω)
      h_x_sq_meas.aestronglyMeasurable h_meas.aemeasurable).symm]
  rw [h_law]
  -- Integrable (fun x => x²) (gaussianReal 0 ⟨t-s, _⟩) via MemLp 2 of id.
  have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
      (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
    ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (⟨t - s, by linarith⟩ : NNReal)) 2
  have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
  convert h using 1
  ext x
  change x^2 = ‖x‖^2
  rw [Real.norm_eq_abs, sq_abs]
end LevyStochCalc.Brownian.Ito


