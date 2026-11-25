-- Prove2me | Definitions.Def_SourceProof_73d7ede32c630ae6f4b43125
-- name    : SourceProof_73d7ede32c630ae6f4b43125
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:55.248688+00:00
-- url     : https://prove2.me/theorems/e4f9ebc7-761b-5c54-a09f-57ffd11f7ab6
-- title:
--   StochLean source theorem: StochLean.tendsto_frechetTaylorErrorCoefficient_of_contDiff

import Definitions.Def_SourceProof_6c8628105866f38712113f22
import Definitions.Def_SourceProof_c0a1798fe7969c16cff73dff

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

theorem _root_.Prove2MeSourceProof.h_73d7ede32c630ae6f4b43125 {α : Type*} {l : Filter α}
    (hf : ContDiff ℝ 2 f) {a b : α → E} {x y : E}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 y)) :
    Tendsto (fun i ↦ frechetTaylorErrorCoefficient f (a i) (b i)) l
      (𝓝 (frechetTaylorErrorCoefficient f x y)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by decide)
  have hH := hd.continuous_fderiv (by decide)
  by_cases h : y = x
  · subst y
    rw [_root_.Prove2MeSourceProof.h_6c8628105866f38712113f22]
    choose θ hθ hbound using fun i ↦ _root_.Prove2MeSourceProof.h_c0a1798fe7969c16cff73dff hf (a i) (b i)
    have hn : Tendsto (fun i ↦ ‖b i - a i‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hb.sub ha).norm
    have hv : Tendsto (fun i ↦ θ i • (b i - a i)) l (𝓝 0) := by
      apply squeeze_zero_norm (fun i ↦ ?_) hn
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ i).2
    have hc : Tendsto (fun i ↦ a i + θ i • (b i - a i)) l (𝓝 x) := by
      simpa only [add_zero] using ha.add hv
    have hbnd : Tendsto (fun i ↦
        ‖fderiv ℝ (fderiv ℝ f) (a i + θ i • (b i - a i)) -
          fderiv ℝ (fderiv ℝ f) (a i)‖ / 2) l (𝓝 0) := by
      simpa only [sub_self, norm_zero, zero_div, Function.comp_apply] using
        ((((hH.tendsto x).comp hc).sub ((hH.tendsto x).comp ha)).norm.div_const 2)
    exact squeeze_zero_norm hbound hbnd
  · have hR : Tendsto (fun i ↦ StochLean.frechetSecondOrderRemainder f (a i) (b i)) l
        (𝓝 (StochLean.frechetSecondOrderRemainder f x y)) := by
      have hc : Continuous (fun p : E × E ↦ StochLean.frechetSecondOrderRemainder f p.1 p.2) := by
        unfold StochLean.frechetSecondOrderRemainder
        fun_prop
      exact (hc.tendsto (x, y)).comp (ha.prodMk_nhds hb)
    exact hR.div ((hb.sub ha).norm.pow 2)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))
end StochLean


