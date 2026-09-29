-- Prove2me | solution 1 for AutomorphicForm.RealIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/35c86eb4-2d56-5a13-bed6-7e34ba008917

import Mathlib
import Theorems.Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay

set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace RealJacquetCont

private noncomputable def uu (x : ℝ) : ℂ := (((x : ℝ) : ℂ) - I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)

private noncomputable def PP (x : ℝ) : ℂ := ((1 + x ^ 2 : ℝ) : ℂ)

private noncomputable def amp (k : ℤ) (w : ℂ) (x : ℝ) : ℂ := uu x ^ k * PP x ^ (-w)

private noncomputable def ker (t x : ℝ) : ℂ := Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * I))

private noncomputable def jj (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := ∫ x : ℝ, amp k w x * ker t x

private theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

private theorem sqrt_pos' (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (one_add_sq_pos x)

private theorem sqrt_ne_zero' (x : ℝ) : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (sqrt_pos' x).ne'

private theorem PP_ne_zero (x : ℝ) : PP x ≠ 0 := ofReal_ne_zero.mpr (one_add_sq_pos x).ne'

private theorem PP_mem_slitPlane (x : ℝ) : PP x ∈ slitPlane := ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

private theorem sqrt_sq_eq (x : ℝ) : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 = PP x := by
  rw [PP, ← ofReal_pow, Real.sq_sqrt (one_add_sq_pos x).le]

private theorem normSq_sub_I (x : ℝ) : Complex.normSq (((x : ℝ) : ℂ) - I) = 1 + x ^ 2 := by
  simp [Complex.normSq_apply]; ring

private theorem norm_sub_I (x : ℝ) : ‖((x : ℝ) : ℂ) - I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_def, normSq_sub_I]

private theorem norm_uu (x : ℝ) : ‖uu x‖ = 1 := by
  rw [uu, norm_div, norm_sub_I, Complex.norm_real, Real.norm_of_nonneg (sqrt_pos' x).le,
    div_self (sqrt_pos' x).ne']

private theorem uu_ne_zero (x : ℝ) : uu x ≠ 0 := fun h => by simpa [h] using norm_uu x

private theorem norm_PP_cpow (w : ℂ) (x : ℝ) : ‖PP x ^ (-w)‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [PP, Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x), neg_re]

private theorem norm_amp (k : ℤ) (w : ℂ) (x : ℝ) : ‖amp k w x‖ = (1 + x ^ 2) ^ (-w.re) := by
  rw [amp, norm_mul, norm_zpow, norm_uu, one_zpow, one_mul, norm_PP_cpow]

private theorem norm_ker (t x : ℝ) : ‖ker t x‖ = 1 := by
  rw [ker, Complex.norm_exp]
  simp

private theorem continuous_uu : Continuous uu := by
  refine Continuous.div (continuous_ofReal.sub continuous_const)
    (continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))))
    fun x => sqrt_ne_zero' x

private theorem continuous_PP : Continuous PP := continuous_ofReal.comp (continuous_const.add (continuous_pow 2))

private theorem continuous_amp (k : ℤ) (w : ℂ) : Continuous (amp k w) := by
  refine Continuous.mul (continuous_uu.zpow₀ k fun x => Or.inl (uu_ne_zero x)) ?_
  exact continuous_PP.cpow continuous_const fun x => PP_mem_slitPlane x

private theorem continuous_ker (t : ℝ) : Continuous (ker t) := by
  unfold ker
  fun_prop

private theorem continuous_ker₂ : Continuous fun p : ℝ × ℝ => ker p.1 p.2 := by
  unfold ker
  fun_prop

private theorem integrable_rpow_neg (σ : ℝ) (hσ : 1 / 2 < σ) : Integrable fun x : ℝ => (1 + x ^ 2) ^ (-σ) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
    (by rw [Module.finrank_self]; push_cast; linarith)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

private theorem integrable_amp_mul (k : ℤ) (w : ℂ) (hw : 1 / 2 < w.re) (F : ℝ → ℂ) (hF : Continuous F)
    (C : ℝ) (hC : ∀ x, ‖F x‖ ≤ C) : Integrable fun x => amp k w x * F x := by
  refine Integrable.mono' ((integrable_rpow_neg w.re hw).mul_const (max C 0))
    ((continuous_amp k w).mul hF).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_amp]
  exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (Real.rpow_nonneg (one_add_sq_pos x).le _)

private theorem integrable_amp_mul_ker (k : ℤ) (w : ℂ) (hw : 1 / 2 < w.re) (t : ℝ) :
    Integrable fun x => amp k w x * ker t x :=
  integrable_amp_mul k w hw (ker t) (continuous_ker t) 1 fun x => (norm_ker t x).le

private theorem tendsto_amp_mul_ker (k : ℤ) (w : ℂ) (hw : 0 < w.re) (t : ℝ) (l : Filter ℝ)
    (hl : Tendsto (fun x : ℝ => 1 + x ^ 2) l atTop) :
    Tendsto (fun x => amp k w x * ker t x) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun x => ‖amp k w x * ker t x‖) = fun x => (1 + x ^ 2) ^ (-w.re) := by
    funext x; rw [norm_mul, norm_amp, norm_ker, mul_one]
  rw [h]
  exact (tendsto_rpow_neg_atTop hw).comp hl

private theorem tendsto_one_add_sq_atTop : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
  tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)

private theorem tendsto_one_add_sq_atBot : Tendsto (fun x : ℝ => 1 + x ^ 2) atBot atTop := by
  have : (fun x : ℝ => 1 + x ^ 2) = (fun x : ℝ => 1 + x ^ 2) ∘ Neg.neg := by funext x; simp
  rw [this]
  exact tendsto_one_add_sq_atTop.comp tendsto_neg_atBot_atTop

end RealJacquetCont

namespace RealJacquetCont

private theorem sub_I_ne_zero (x : ℝ) : ((x : ℝ) : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem _root_.RealJacquetCont.hasDerivAt_sqrt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2)) (x / Real.sqrt (1 + x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).const_add 1)
  have h2 := (Real.hasDerivAt_sqrt (one_add_sq_pos x).ne').comp x h1
  refine h2.congr_deriv ?_
  field_simp

p2m_export "RealJacquetCont" "hasDerivAt_sqrt"
private theorem hasDerivAt_uu (x : ℝ) : HasDerivAt uu (I * uu x / PP x) x := by
  have hN : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) - I) 1 x :=
    (Complex.ofRealCLM.hasDerivAt.sub_const I).congr_deriv (by simp)
  have hD : HasDerivAt (fun y : ℝ => ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ))
      (((x : ℝ) : ℂ) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) x :=
    (hasDerivAt_sqrt x).ofReal_comp.congr_deriv (by push_cast; ring)
  have h := hN.div hD (sqrt_ne_zero' x)
  refine h.congr_deriv ?_
  have hs : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero' x
  have hs2 : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 = 1 + ((x : ℝ) : ℂ) ^ 2 := by
    rw [sqrt_sq_eq, PP]; push_cast; ring
  rw [uu, ← sqrt_sq_eq]
  field_simp
  linear_combination hs2 + Complex.I_sq

private theorem hasDerivAt_PP_cpow (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => PP y ^ (-w)) (-w * PP x ^ (-w - 1) * (2 * ((x : ℝ) : ℂ))) x := by
  have hP : HasDerivAt PP (2 * ((x : ℝ) : ℂ)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_add 1)
    exact h1.ofReal_comp.congr_deriv (by push_cast; ring)
  have h₂ : HasDerivAt (fun z : ℂ => z ^ (-w)) (-w * PP x ^ (-w - 1)) (PP x) :=
    (Complex.hasStrictDerivAt_cpow_const (Or.inl (by rw [PP, ofReal_re]; exact one_add_sq_pos x))).hasDerivAt
  exact h₂.comp x hP

private theorem hasDerivAt_uu_zpow (k : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => uu y ^ k) ((k : ℂ) * uu x ^ (k - 1) * (I * uu x / PP x)) x :=
  (hasDerivAt_zpow k (uu x) (Or.inl (uu_ne_zero x))).comp x (hasDerivAt_uu x)

private theorem uu_add_inv (x : ℝ) : uu x + (uu x)⁻¹ = 2 * ((x : ℝ) : ℂ) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  have hs : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero' x
  have hs2 : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 = 1 + ((x : ℝ) : ℂ) ^ 2 := by
    rw [sqrt_sq_eq, PP]; push_cast; ring
  have hxI := sub_I_ne_zero x
  rw [uu, inv_div]
  field_simp
  linear_combination hs2 + Complex.I_sq

private theorem PP_cpow_half (x : ℝ) : PP x ^ ((1 / 2 : ℂ)) = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  rw [PP, Real.sqrt_eq_rpow, Complex.ofReal_cpow (one_add_sq_pos x).le]
  norm_num

private theorem amp_deriv_eq (k : ℤ) (w : ℂ) (x : ℝ) :
    (k : ℂ) * uu x ^ (k - 1) * (I * uu x / PP x) * PP x ^ (-w)
        + uu x ^ k * (-w * PP x ^ (-w - 1) * (2 * ((x : ℝ) : ℂ)))
      = I * k * amp k (w + 1) x - w * amp (k + 1) (w + 1 / 2) x - w * amp (k - 1) (w + 1 / 2) x := by
  have hP0 := PP_ne_zero x
  have hU0 := uu_ne_zero x
  have hs : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero' x

  have e1 : PP x ^ (-(w + 1)) = PP x ^ (-w) * (PP x)⁻¹ := by
    rw [neg_add, Complex.cpow_add _ _ hP0, Complex.cpow_neg_one]
  have e2 : PP x ^ (-w - 1) = PP x ^ (-w) * (PP x)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hP0, Complex.cpow_neg_one]
  have e3 : PP x ^ (-(w + 1 / 2)) = PP x ^ (-w) * (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ))⁻¹ := by
    rw [neg_add, Complex.cpow_add _ _ hP0, Complex.cpow_neg (PP x) (1 / 2 : ℂ), PP_cpow_half]
  have u1 : uu x ^ (k + 1) = uu x ^ k * uu x := zpow_add_one₀ hU0 k
  have u2 : uu x ^ (k - 1) = uu x ^ k * (uu x)⁻¹ := zpow_sub_one₀ hU0 k
  have hx2 : 2 * ((x : ℝ) : ℂ) = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) * (uu x + (uu x)⁻¹) := by
    rw [uu_add_inv]; field_simp
  have hPs : PP x = ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 := (sqrt_sq_eq x).symm
  simp only [amp, e1, e2, e3, u1, u2, hx2]
  rw [hPs]
  field_simp
  ring

private theorem hasDerivAt_amp (k : ℤ) (w : ℂ) (x : ℝ) :
    HasDerivAt (amp k w)
      (I * k * amp k (w + 1) x - w * amp (k + 1) (w + 1 / 2) x - w * amp (k - 1) (w + 1 / 2) x) x := by
  have h := (hasDerivAt_uu_zpow k x).mul (hasDerivAt_PP_cpow w x)
  rw [← amp_deriv_eq]
  exact h

private theorem hasDerivAt_ker (t x : ℝ) :
    HasDerivAt (ker t) (-(((2 * Real.pi * t : ℝ) : ℂ) * I) * ker t x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(((2 * Real.pi * t * y : ℝ) : ℂ) * I)) (-(((2 * Real.pi * t : ℝ) : ℂ) * I)) x := by
    have h : HasDerivAt (fun y : ℝ => ((2 * Real.pi * t * y : ℝ) : ℂ)) (((2 * Real.pi * t : ℝ) : ℂ)) x := by
      have := ((hasDerivAt_id x).const_mul (2 * Real.pi * t)).ofReal_comp
      simpa using this
    exact (h.mul_const I).neg
  have h2 := h1.cexp
  refine h2.congr_deriv ?_
  rw [ker]
  ring

end RealJacquetCont

namespace RealJacquetCont

private theorem jj_halfplane (k : ℤ) :
    ContinuousOn (fun q : ℂ × ℝ => jj k q.1 q.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => jj k w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖jj k w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) :=
  AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral k

private noncomputable def cc (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * I

private theorem cc_ne_zero (t : ℝ) (ht : t ≠ 0) : cc t ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr (by positivity)) I_ne_zero

private theorem norm_cc (t : ℝ) : ‖cc t‖ = 2 * Real.pi * |t| := by
  rw [cc, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_two]

private theorem jj_step (k : ℤ) (w : ℂ) (hw : 1 / 2 < w.re) (t : ℝ) (ht : t ≠ 0) :
    jj k w t = (cc t)⁻¹ *
      (I * k * jj k (w + 1) t - w * jj (k + 1) (w + 1 / 2) t - w * jj (k - 1) (w + 1 / 2) t) := by
  have hw0 : 0 < w.re := by linarith
  have hw1 : 1 / 2 < (w + 1).re := by simp; linarith
  have hw2 : 1 / 2 < (w + 1 / 2).re := by simp; norm_num; linarith
  set u' : ℝ → ℂ := fun x =>
    I * k * amp k (w + 1) x - w * amp (k + 1) (w + 1 / 2) x - w * amp (k - 1) (w + 1 / 2) x with hu'
  set v' : ℝ → ℂ := fun x => -cc t * ker t x with hv'
  have hu : ∀ x ∈ tsupport (ker t), HasDerivAt (amp k w) (u' x) x := fun x _ => hasDerivAt_amp k w x
  have hv : ∀ x ∈ tsupport (amp k w), HasDerivAt (ker t) (v' x) x := fun x _ => by
    simpa [hv', cc] using hasDerivAt_ker t x
  have huv' : Integrable (amp k w * v') := by
    show Integrable fun x => amp k w x * (-cc t * ker t x)
    exact integrable_amp_mul k w hw _ (continuous_const.mul (continuous_ker t)) ‖cc t‖
      fun x => by rw [norm_mul, norm_neg, norm_ker, mul_one]
  have hI1 := integrable_amp_mul_ker k (w + 1) hw1 t
  have hI2 := integrable_amp_mul_ker (k + 1) (w + 1 / 2) hw2 t
  have hI3 := integrable_amp_mul_ker (k - 1) (w + 1 / 2) hw2 t
  have hu'v_eq : (u' * ker t) = fun x => I * k * (amp k (w + 1) x * ker t x)
      - w * (amp (k + 1) (w + 1 / 2) x * ker t x) - w * (amp (k - 1) (w + 1 / 2) x * ker t x) := by
    funext x
    simp only [Pi.mul_apply, hu']
    ring
  have hu'v : Integrable (u' * ker t) := by
    rw [hu'v_eq]
    exact ((hI1.const_mul _).sub (hI2.const_mul _)).sub (hI3.const_mul _)
  have hbot : Tendsto (amp k w * ker t) atBot (𝓝 0) := tendsto_amp_mul_ker k w hw0 t _ tendsto_one_add_sq_atBot
  have htop : Tendsto (amp k w * ker t) atTop (𝓝 0) := tendsto_amp_mul_ker k w hw0 t _ tendsto_one_add_sq_atTop
  have hparts := integral_mul_deriv_eq_deriv_mul hu hv huv' hu'v hbot htop

  have hL : ∫ x, amp k w x * v' x = -cc t * jj k w t := by
    rw [jj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hv']
    ring

  have hR : ∫ x, u' x * ker t x = I * k * jj k (w + 1) t - w * jj (k + 1) (w + 1 / 2) t
      - w * jj (k - 1) (w + 1 / 2) t := by
    have h := congrFun hu'v_eq
    simp only [Pi.mul_apply] at h
    simp_rw [h]
    rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
    · rfl
    · exact hI1.const_mul _
    · exact hI2.const_mul _
    · exact (hI1.const_mul _).sub' (hI2.const_mul _)
    · exact hI3.const_mul _
  rw [hL, hR, sub_zero, zero_sub] at hparts
  have hc := cc_ne_zero t ht
  rw [eq_inv_mul_iff_mul_eq₀ hc]
  linear_combination -hparts

end RealJacquetCont

namespace RealJacquetCont

private noncomputable def TT (G : ℤ → ℂ → ℝ → ℂ) : ℤ → ℂ → ℝ → ℂ := fun k w t =>
  (cc t)⁻¹ * (I * k * G k (w + 1) t - w * G (k + 1) (w + 1 / 2) t - w * G (k - 1) (w + 1 / 2) t)

private noncomputable def iter (M : ℕ) : ℤ → ℂ → ℝ → ℂ := (TT^[M]) jj

private theorem iter_zero : iter 0 = jj := rfl

private theorem iter_succ (M : ℕ) : iter (M + 1) = TT (iter M) := Function.iterate_succ_apply' TT M jj

private theorem iter_succ' (M : ℕ) : iter (M + 1) = (TT^[M]) (TT jj) := Function.iterate_succ_apply TT M jj

private theorem re_add_one (w : ℂ) : (w + 1).re = w.re + 1 := by simp

private theorem re_add_half (w : ℂ) : (w + 1 / 2).re = w.re + 1 / 2 := by simp

private theorem TT_jj (k : ℤ) (w : ℂ) (t : ℝ) (hw : 1 / 2 < w.re) (ht : t ≠ 0) : TT jj k w t = jj k w t :=
  (jj_step k w hw t ht).symm

private theorem TT_congr {G G' : ℤ → ℂ → ℝ → ℂ} {c : ℝ}
    (h : ∀ (k : ℤ) (w : ℂ) (t : ℝ), c < w.re → t ≠ 0 → G k w t = G' k w t)
    (k : ℤ) (w : ℂ) (t : ℝ) (hw : c - 1 / 2 < w.re) (ht : t ≠ 0) : TT G k w t = TT G' k w t := by
  simp only [TT]
  rw [h k (w + 1) t (by rw [re_add_one]; linarith) ht, h (k + 1) (w + 1 / 2) t (by rw [re_add_half]; linarith) ht,
    h (k - 1) (w + 1 / 2) t (by rw [re_add_half]; linarith) ht]

private theorem iterate_TT_congr (M : ℕ) : ∀ {G G' : ℤ → ℂ → ℝ → ℂ} {c : ℝ},
    (∀ (k : ℤ) (w : ℂ) (t : ℝ), c < w.re → t ≠ 0 → G k w t = G' k w t) →
    ∀ (k : ℤ) (w : ℂ) (t : ℝ), c - M / 2 < w.re → t ≠ 0 → (TT^[M]) G k w t = (TT^[M]) G' k w t := by
  induction M with
  | zero => intro G G' c h k w t hw ht; exact h k w t (by simpa using hw) ht
  | succ M ih =>
    intro G G' c h k w t hw ht
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine TT_congr (c := c - M / 2) (ih h) k w t ?_ ht
    push_cast at hw ⊢
    linarith

private theorem iter_eq_jj (M : ℕ) : ∀ (k : ℤ) (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → iter M k w t = jj k w t := by
  induction M with
  | zero => intro k w t _ _; rfl
  | succ M ih =>
    intro k w t hw ht
    rw [iter_succ, TT_congr (c := 1 / 2) ih k w t (by linarith) ht]
    exact TT_jj k w t hw ht

private theorem iter_succ_eq (M : ℕ) (k : ℤ) (w : ℂ) (t : ℝ) (hw : 1 / 2 - M / 2 < w.re) (ht : t ≠ 0) :
    iter (M + 1) k w t = iter M k w t := by
  rw [iter_succ', iter]
  exact iterate_TT_congr M (c := 1 / 2) (fun k w t hw ht => TT_jj k w t hw ht) k w t hw ht

private theorem iter_eq_iter_of_le {M M' : ℕ} (hMM : M ≤ M') (k : ℤ) (w : ℂ) (t : ℝ) (hw : 1 / 2 - M / 2 < w.re)
    (ht : t ≠ 0) : iter M' k w t = iter M k w t := by
  induction M', hMM using Nat.le_induction with
  | base => rfl
  | succ M' hMM' ih =>
    rw [← ih]
    refine iter_succ_eq M' k w t ?_ ht
    have : (M : ℝ) ≤ M' := by exact_mod_cast hMM'
    linarith

private noncomputable def Mof (w : ℂ) : ℕ := ⌈1 - 2 * w.re⌉₊ + 1

private theorem Mof_spec (w : ℂ) : 1 / 2 - (Mof w : ℝ) / 2 < w.re := by
  have h := Nat.le_ceil (1 - 2 * w.re)
  simp only [Mof]
  push_cast
  linarith

private noncomputable def JJ (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := iter (Mof w) k w t

private theorem JJ_eq_iter (k : ℤ) (M : ℕ) (w : ℂ) (t : ℝ) (hw : 1 / 2 - M / 2 < w.re) (ht : t ≠ 0) :
    JJ k w t = iter M k w t := by
  unfold JJ
  rcases le_total M (Mof w) with h | h
  · exact iter_eq_iter_of_le h k w t hw ht
  · exact (iter_eq_iter_of_le h k w t (Mof_spec w) ht).symm

private theorem isOpen_re_gt (c : ℝ) : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem TT_differentiableOn {G : ℤ → ℂ → ℝ → ℂ} {c : ℝ}
    (h : ∀ (k : ℤ) (t : ℝ), t ≠ 0 → DifferentiableOn ℂ (fun w => G k w t) {w : ℂ | c < w.re})
    (k : ℤ) (t : ℝ) (ht : t ≠ 0) : DifferentiableOn ℂ (fun w => TT G k w t) {w : ℂ | c - 1 / 2 < w.re} := by
  have h1 : DifferentiableOn ℂ (fun w => G k (w + 1) t) {w : ℂ | c - 1 / 2 < w.re} :=
    (h k t ht).comp (differentiable_id.add_const 1).differentiableOn fun w hw => by
      simp only [mem_setOf_eq, re_add_one] at hw ⊢; linarith
  have h2 : ∀ k', DifferentiableOn ℂ (fun w => G k' (w + 1 / 2) t) {w : ℂ | c - 1 / 2 < w.re} := fun k' =>
    (h k' t ht).comp (differentiable_id.add_const _).differentiableOn fun w hw => by
      simp only [mem_setOf_eq, re_add_half] at hw ⊢; linarith
  simp only [TT]
  exact (DifferentiableOn.const_mul ((((differentiableOn_const _).mul h1).sub (differentiableOn_id.mul (h2 _))).sub
    (differentiableOn_id.mul (h2 _))) _)

private theorem region_succ (M : ℕ) :
    {w : ℂ | 1 / 2 - ((M + 1 : ℕ) : ℝ) / 2 < w.re} = {w : ℂ | (1 / 2 - (M : ℝ) / 2) - 1 / 2 < w.re} := by
  ext w
  simp only [mem_setOf_eq]
  push_cast
  constructor <;> intro h <;> linarith

private theorem iter_differentiableOn (M : ℕ) : ∀ (k : ℤ) (t : ℝ), t ≠ 0 →
    DifferentiableOn ℂ (fun w => iter M k w t) {w : ℂ | 1 / 2 - M / 2 < w.re} := by
  induction M with
  | zero => intro k t _; simpa [iter_zero] using (jj_halfplane k).2.1 t
  | succ M ih =>
    intro k t ht
    rw [iter_succ, region_succ]
    exact TT_differentiableOn (c := 1 / 2 - M / 2) ih k t ht

private theorem differentiable_JJ (k : ℤ) (t : ℝ) (ht : t ≠ 0) : Differentiable ℂ (fun w => JJ k w t) := by
  intro w₀
  set M := Mof w₀
  have hU : {w : ℂ | 1 / 2 - M / 2 < w.re} ∈ 𝓝 w₀ := (isOpen_re_gt _).mem_nhds (Mof_spec w₀)
  have hd : DifferentiableAt ℂ (fun w => iter M k w t) w₀ := (iter_differentiableOn M k t ht).differentiableAt hU
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hU] with w hw
  exact JJ_eq_iter k M w t hw ht

private theorem JJ_eq_jj (k : ℤ) (w : ℂ) (t : ℝ) (hw : 1 / 2 < w.re) (ht : t ≠ 0) : JJ k w t = jj k w t := by
  unfold JJ
  exact iter_eq_jj _ k w t hw ht

private theorem continuous_cc : Continuous cc := by
  unfold cc; fun_prop

private theorem TT_continuousOn {G : ℤ → ℂ → ℝ → ℂ} {c : ℝ}
    (h : ∀ k : ℤ, ContinuousOn (fun p : ℂ × ℝ => G k p.1 p.2) ({w : ℂ | c < w.re} ×ˢ {t : ℝ | t ≠ 0}))
    (k : ℤ) : ContinuousOn (fun p : ℂ × ℝ => TT G k p.1 p.2) ({w : ℂ | c - 1 / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) := by
  have hcc : ContinuousOn (fun p : ℂ × ℝ => (cc p.2)⁻¹) ({w : ℂ | c - 1 / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) :=
    (continuous_cc.comp continuous_snd).continuousOn.inv₀ fun p hp => cc_ne_zero p.2 hp.2
  have h1 : ContinuousOn (fun p : ℂ × ℝ => G k (p.1 + 1) p.2) ({w : ℂ | c - 1 / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) := by
    refine (h k).comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn fun p hp => ?_
    simp only [mem_prod, mem_setOf_eq, Pi.add_apply, re_add_one] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  have h2 : ∀ k', ContinuousOn (fun p : ℂ × ℝ => G k' (p.1 + 1 / 2) p.2)
      ({w : ℂ | c - 1 / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) := by
    intro k'
    refine (h k').comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn fun p hp => ?_
    simp only [mem_prod, mem_setOf_eq, Pi.add_apply, re_add_half] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  simp only [TT]
  exact hcc.mul (((continuousOn_const.mul h1).sub (continuous_fst.continuousOn.mul (h2 _))).sub
    (continuous_fst.continuousOn.mul (h2 _)))

private theorem iter_continuousOn (M : ℕ) : ∀ k : ℤ,
    ContinuousOn (fun p : ℂ × ℝ => iter M k p.1 p.2) ({w : ℂ | 1 / 2 - M / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) := by
  induction M with
  | zero =>
    intro k
    have h := (jj_halfplane k).1
    simp only [iter_zero, CharP.cast_eq_zero, zero_div, sub_zero]
    exact h.mono (prod_mono le_rfl (subset_univ _))
  | succ M ih =>
    intro k
    rw [iter_succ, region_succ]
    exact TT_continuousOn (c := 1 / 2 - M / 2) ih k

private theorem continuousOn_JJ (k : ℤ) : ContinuousOn (fun p : ℂ × ℝ => JJ k p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) := by
  intro p hp
  obtain ⟨w₀, t₀⟩ := p
  have ht₀ : t₀ ≠ 0 := hp.2
  set M := Mof w₀
  have hV : ({w : ℂ | 1 / 2 - M / 2 < w.re} ×ˢ {t : ℝ | t ≠ 0}) ∈ 𝓝 (w₀, t₀) :=
    ((isOpen_re_gt _).prod (isOpen_ne)).mem_nhds ⟨Mof_spec w₀, ht₀⟩
  have hc : ContinuousAt (fun p : ℂ × ℝ => iter M k p.1 p.2) (w₀, t₀) := (iter_continuousOn M k).continuousAt hV
  refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [hV] with p hp'
  exact JJ_eq_iter k M p.1 p.2 hp'.1 hp'.2

end RealJacquetCont

namespace RealJacquetCont

private def BoundOn (G : ℤ → ℂ → ℝ → ℂ) (c : ℝ) (m : ℕ) : Prop :=
  ∀ (k : ℤ) (K : Set ℂ), IsCompact K → K ⊆ {w : ℂ | c < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖G k w t‖ ≤ C * |t| ^ (-(m : ℝ)) * (1 + |t|) ^ (-(N : ℝ))

private theorem norm_cc_inv (t : ℝ) : ‖(cc t)⁻¹‖ = (2 * Real.pi)⁻¹ * |t| ^ (-(1 : ℝ)) := by
  rw [norm_inv, norm_cc, Real.rpow_neg_one, mul_inv]

private theorem TT_boundOn {G : ℤ → ℂ → ℝ → ℂ} {c : ℝ} {m : ℕ} (h : BoundOn G c m) :
    BoundOn (TT G) (c - 1 / 2) (m + 1) := by
  intro k K hK hKsub N

  have hK1 : IsCompact ((fun w : ℂ => w + 1) '' K) := hK.image (continuous_id.add continuous_const)
  have hK2 : IsCompact ((fun w : ℂ => w + 1 / 2) '' K) := hK.image (continuous_id.add continuous_const)
  have hK1sub : (fun w : ℂ => w + 1) '' K ⊆ {w : ℂ | c < w.re} := by
    rintro _ ⟨w, hw, rfl⟩
    have := hKsub hw
    simp only [mem_setOf_eq, re_add_one] at this ⊢
    linarith
  have hK2sub : (fun w : ℂ => w + 1 / 2) '' K ⊆ {w : ℂ | c < w.re} := by
    rintro _ ⟨w, hw, rfl⟩
    have := hKsub hw
    simp only [mem_setOf_eq, re_add_half] at this ⊢
    linarith
  obtain ⟨C₁, hC₁, h₁⟩ := h k _ hK1 hK1sub N
  obtain ⟨C₂, hC₂, h₂⟩ := h (k + 1) _ hK2 hK2sub N
  obtain ⟨C₃, hC₃, h₃⟩ := h (k - 1) _ hK2 hK2sub N
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  set C : ℝ := (2 * Real.pi)⁻¹ * ((|(k : ℝ)| + 1) * C₁ + (|R| + 1) * (C₂ + C₃)) with hCdef
  have hpi : 0 < (2 * Real.pi)⁻¹ := by positivity
  refine ⟨C, by positivity, fun w hw t ht => ?_⟩
  have ht0 : 0 < |t| := abs_pos.mpr ht
  set X : ℝ := |t| ^ (-(m : ℝ)) * (1 + |t|) ^ (-(N : ℝ)) with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (by positivity) _)
  have hw' : ‖w‖ ≤ |R| := (hR w hw).trans (le_abs_self R)
  have b₁ : ‖G k (w + 1) t‖ ≤ C₁ * X := by rw [hX, ← mul_assoc]; exact h₁ _ ⟨w, hw, rfl⟩ t ht
  have b₂ : ‖G (k + 1) (w + 1 / 2) t‖ ≤ C₂ * X := by rw [hX, ← mul_assoc]; exact h₂ _ ⟨w, hw, rfl⟩ t ht
  have b₃ : ‖G (k - 1) (w + 1 / 2) t‖ ≤ C₃ * X := by rw [hX, ← mul_assoc]; exact h₃ _ ⟨w, hw, rfl⟩ t ht
  have hk : ‖(I * k : ℂ)‖ ≤ |(k : ℝ)| + 1 := by
    rw [norm_mul, norm_I, one_mul, Complex.norm_intCast]; linarith
  have n1 : ‖I * k * G k (w + 1) t‖ ≤ (|(k : ℝ)| + 1) * (C₁ * X) := by
    rw [norm_mul]; exact mul_le_mul hk b₁ (norm_nonneg _) (by positivity)
  have n2 : ‖w * G (k + 1) (w + 1 / 2) t‖ ≤ (|R| + 1) * (C₂ * X) := by
    rw [norm_mul]; exact mul_le_mul (hw'.trans (by linarith)) b₂ (norm_nonneg _) (by positivity)
  have n3 : ‖w * G (k - 1) (w + 1 / 2) t‖ ≤ (|R| + 1) * (C₃ * X) := by
    rw [norm_mul]; exact mul_le_mul (hw'.trans (by linarith)) b₃ (norm_nonneg _) (by positivity)
  have hsum : ‖I * k * G k (w + 1) t - w * G (k + 1) (w + 1 / 2) t - w * G (k - 1) (w + 1 / 2) t‖
      ≤ ((|(k : ℝ)| + 1) * C₁ + (|R| + 1) * (C₂ + C₃)) * X :=
    calc ‖I * k * G k (w + 1) t - w * G (k + 1) (w + 1 / 2) t - w * G (k - 1) (w + 1 / 2) t‖
        ≤ ‖I * k * G k (w + 1) t - w * G (k + 1) (w + 1 / 2) t‖ + ‖w * G (k - 1) (w + 1 / 2) t‖ :=
          norm_sub_le _ _
      _ ≤ (‖I * k * G k (w + 1) t‖ + ‖w * G (k + 1) (w + 1 / 2) t‖) + ‖w * G (k - 1) (w + 1 / 2) t‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ((|(k : ℝ)| + 1) * (C₁ * X) + (|R| + 1) * (C₂ * X)) + (|R| + 1) * (C₃ * X) :=
          add_le_add (add_le_add n1 n2) n3
      _ = _ := by ring
  simp only [TT]
  rw [norm_mul, norm_cc_inv]
  have hexp : (-(1 : ℝ)) + (-(m : ℝ)) = -((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hpow : |t| ^ (-(1 : ℝ)) * X = |t| ^ (-((m + 1 : ℕ) : ℝ)) * (1 + |t|) ^ (-(N : ℝ)) := by
    rw [hX, ← mul_assoc, ← Real.rpow_add ht0, hexp]
  calc (2 * Real.pi)⁻¹ * |t| ^ (-(1 : ℝ)) *
        ‖I * k * G k (w + 1) t - w * G (k + 1) (w + 1 / 2) t - w * G (k - 1) (w + 1 / 2) t‖
      ≤ (2 * Real.pi)⁻¹ * |t| ^ (-(1 : ℝ)) * (((|(k : ℝ)| + 1) * C₁ + (|R| + 1) * (C₂ + C₃)) * X) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hpi.le (Real.rpow_nonneg (abs_nonneg _) _))
    _ = C * (|t| ^ (-(1 : ℝ)) * X) := by rw [hCdef]; ring
    _ = C * |t| ^ (-((m + 1 : ℕ) : ℝ)) * (1 + |t|) ^ (-(N : ℝ)) := by rw [hpow, hCdef]; ring

private theorem jj_boundOn : BoundOn jj (1 / 2) 0 := by
  intro k K hK hKsub N
  obtain ⟨C, hC, h⟩ := (jj_halfplane k).2.2 K hK hKsub N
  refine ⟨C, hC, fun w hw t _ => ?_⟩
  rw [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
  exact h w hw t

private theorem iter_boundOn (M : ℕ) : BoundOn (iter M) (1 / 2 - M / 2) M := by
  induction M with
  | zero => simpa [iter_zero] using jj_boundOn
  | succ M ih =>
    have hc : (1 / 2 - ((M + 1 : ℕ) : ℝ) / 2) = 1 / 2 - (M : ℝ) / 2 - 1 / 2 := by push_cast; ring
    rw [iter_succ, hc]
    exact TT_boundOn ih

private theorem JJ_bound (k : ℤ) (K : Set ℂ) (hK : IsCompact K) : ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖JJ k w t‖ ≤ C * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ)) := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  set M : ℕ := ⌈2 * |R| + 1⌉₊ + 1 with hM
  have hKsub : K ⊆ {w : ℂ | 1 / 2 - M / 2 < w.re} := by
    intro w hw
    have h1 : ‖w‖ ≤ |R| := (hR w hw).trans (le_abs_self R)
    have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h3 : -|R| ≤ w.re := by linarith [neg_abs_le w.re]
    have h4 := Nat.le_ceil (2 * |R| + 1)
    simp only [mem_setOf_eq, hM]
    push_cast
    linarith
  refine ⟨M, fun N => ?_⟩
  obtain ⟨C, hC, h⟩ := iter_boundOn M k K hK hKsub N
  refine ⟨C, hC, fun w hw t ht => ?_⟩
  rw [JJ_eq_iter k M w t (hKsub hw) ht]
  exact h w hw t ht

end RealJacquetCont

open RealJacquetCont in
theorem solution (k : ℤ) :
    let j : ℂ → ℝ → ℂ := fun w t => ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → J w t = j w t) ∧
      ContinuousOn (fun p : ℂ × ℝ => J p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖J w t‖ ≤ C * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ))) := by
  intro j
  refine ⟨JJ k, fun t ht => differentiable_JJ k t ht, fun w t hw ht => ?_, continuousOn_JJ k, JJ_bound k⟩
  rw [JJ_eq_jj k w t hw ht]
  rfl

end S_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
end P2MW
export P2MW.S_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay (solution)
