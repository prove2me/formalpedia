-- Prove2me | solution 1 for Arxivmath_ph_0108008.ct_nontrivial_solution
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T07:25:02.131548+00:00
-- url     : https://prove2.me/submissions/872b3790-03db-4cad-a1dd-7b5d9e5e6672

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

noncomputable section
namespace CTX

lemma nonneg_of_deriv (F F' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x) (h0 : F 0 = 0)
    (hpos : ∀ x, 0 < x → 0 ≤ F' x) (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F t := by
  have hm : MonotoneOn F (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hF x).continuousAt.continuousWithinAt)
      (fun x _ => (hF x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [interior_Ici] at hx
        rw [(hF x).deriv]; exact hpos x hx)
  have := hm (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 ht) ht
  linarith

def M (x : ℝ) : ℝ := Real.sin x - x * Real.cos x
def N (x : ℝ) : ℝ := 3 * Real.sin x - 3 * x * Real.cos x - x ^ 2 * Real.sin x

lemma hasDerivM (x : ℝ) : HasDerivAt M (x * Real.sin x) x := by
  have h1 : HasDerivAt (fun y => Real.sin y - y * Real.cos y)
      (Real.cos x - (1 * Real.cos x + x * (-Real.sin x))) x :=
    (Real.hasDerivAt_sin x).sub ((hasDerivAt_id' x).mul (Real.hasDerivAt_cos x))
  exact h1.congr_deriv (by ring)

lemma hasDerivN (x : ℝ) : HasDerivAt N (x * M x) x := by
  have := (((Real.hasDerivAt_sin x).const_mul 3).sub
      (((hasDerivAt_id' x).const_mul 3).mul (Real.hasDerivAt_cos x))).sub
      ((hasDerivAt_pow 2 x).mul (Real.hasDerivAt_sin x))
  exact this.congr_deriv (by simp [M]; ring)

lemma M_bound (t : ℝ) (ht : 0 ≤ t) : |M t| ≤ t ^ 3 / 3 := by
  have hs := fun x : ℝ => Real.abs_sin_le_abs (x := x)
  rw [abs_le]; constructor
  · have := nonneg_of_deriv (fun x => x ^ 3 / 3 + M x) (fun x => x ^ 2 + x * Real.sin x)
      (fun x => by
        have := ((hasDerivAt_pow 3 x).div_const 3).add (hasDerivM x)
        exact this.congr_deriv (by push_cast; ring))
      (by simp [M]) (fun x hx => by
        have := hs x
        rw [abs_of_pos hx] at this
        have := (abs_le.1 this).1
        nlinarith) t ht
    linarith
  · have := nonneg_of_deriv (fun x => x ^ 3 / 3 - M x) (fun x => x ^ 2 - x * Real.sin x)
      (fun x => by
        have := ((hasDerivAt_pow 3 x).div_const 3).sub (hasDerivM x)
        exact this.congr_deriv (by push_cast; ring))
      (by simp [M]) (fun x hx => by
        have := Real.sin_le hx.le
        nlinarith) t ht
    linarith

lemma N_bound (t : ℝ) (ht : 0 ≤ t) : |N t| ≤ t ^ 5 / 15 := by
  rw [abs_le]; constructor
  · have := nonneg_of_deriv (fun x => x ^ 5 / 15 + N x) (fun x => x ^ 4 / 3 + x * M x)
      (fun x => by
        have := ((hasDerivAt_pow 5 x).div_const 15).add (hasDerivN x)
        exact this.congr_deriv (by push_cast; ring))
      (by simp [N]) (fun x hx => by
        have := (abs_le.1 (M_bound x hx.le)).1
        nlinarith) t ht
    linarith
  · have := nonneg_of_deriv (fun x => x ^ 5 / 15 - N x) (fun x => x ^ 4 / 3 - x * M x)
      (fun x => by
        have := ((hasDerivAt_pow 5 x).div_const 15).sub (hasDerivN x)
        exact this.congr_deriv (by push_cast; ring))
      (by simp [N]) (fun x hx => by
        have := (abs_le.1 (M_bound x hx.le)).2
        nlinarith) t ht
    linarith

open Arxivmath_ph_0108008

def D (x : ℝ) : ℝ := (3 / x - 6 / x ^ 3) * Real.sin x + (6 / x ^ 2 - 1) * Real.cos x
def FA (x : ℝ) : ℝ := Real.sin x * D x - Real.cos x * riccatiU2 x
def FB (x : ℝ) : ℝ := Real.cos x * D x + Real.sin x * riccatiU2 x

lemma u2_eq (t : ℝ) (ht : t ≠ 0) : riccatiU2 t = N t / t ^ 2 := by
  unfold riccatiU2 N; field_simp; ring

lemma D_eq (t : ℝ) (ht : t ≠ 0) : D t = M t / t - 2 * N t / t ^ 3 := by
  unfold D M N; field_simp; ring

lemma u2_bound (t : ℝ) (ht : 0 ≤ t) : |riccatiU2 t| ≤ t ^ 3 / 15 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [riccatiU2]
  · rw [u2_eq t h.ne', abs_div, abs_of_pos (pow_pos h 2), div_le_iff₀ (pow_pos h 2)]
    have := N_bound t h.le
    nlinarith [show t ^ 3 / 15 * t ^ 2 = t ^ 5 / 15 by ring]

lemma D_bound (t : ℝ) (h : 0 < t) : |D t| ≤ 7 * t ^ 2 / 15 := by
  · rw [D_eq t h.ne']
    have h1 : |M t / t| ≤ t ^ 2 / 3 := by
      rw [abs_div, abs_of_pos h, div_le_iff₀ h]
      have := M_bound t h.le
      nlinarith [show t ^ 2 / 3 * t = t ^ 3 / 3 by ring]
    have h2 : |2 * N t / t ^ 3| ≤ 2 * t ^ 2 / 15 := by
      rw [abs_div, abs_of_pos (pow_pos h 3), div_le_iff₀ (pow_pos h 3), abs_mul]
      have := N_bound t h.le
      norm_num
      nlinarith [show 2 * t ^ 2 / 15 * t ^ 3 = 2 * (t ^ 5 / 15) by ring]
    have := abs_sub (M t / t) (2 * N t / t ^ 3)
    linarith

lemma FA_bound (t : ℝ) (ht : 0 ≤ t) : |FA t| ≤ 7 * t ^ 2 / 15 + t ^ 3 / 15 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [FA, riccatiU2]
  unfold FA
  have h1 := abs_sub (Real.sin t * D t) (Real.cos t * riccatiU2 t)
  rw [abs_mul, abs_mul] at h1
  have := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg (D t))
  have := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg (riccatiU2 t))
  have := D_bound t h
  have := u2_bound t ht
  linarith

lemma hu2 (x : ℝ) (hx : x ≠ 0) : HasDerivAt riccatiU2 (D x) x := by
  have := ((((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)).sub_const 1).mul
    (Real.hasDerivAt_sin x)).sub
    (((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_id' x) hx).mul (Real.hasDerivAt_cos x))
  exact this.congr_deriv (by simp only [Pi.div_apply]; unfold D; field_simp; ring)

lemma hD (x : ℝ) (hx : x ≠ 0) : HasDerivAt D (6 * riccatiU2 x / x ^ 2 - riccatiU2 x) x := by
  have := ((((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_id' x) hx).sub
    ((hasDerivAt_const x (6:ℝ)).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx))).mul
    (Real.hasDerivAt_sin x)).add
    ((((hasDerivAt_const x (6:ℝ)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)).sub_const 1).mul
    (Real.hasDerivAt_cos x))
  exact this.congr_deriv (by simp only [Pi.div_apply, Pi.sub_apply]; unfold riccatiU2; field_simp; ring)

lemma hFA (x : ℝ) (hx : x ≠ 0) : HasDerivAt FA (6 * Real.sin x * riccatiU2 x * (x ^ 2)⁻¹) x := by
  have := ((Real.hasDerivAt_sin x).mul (hD x hx)).sub ((Real.hasDerivAt_cos x).mul (hu2 x hx))
  exact this.congr_deriv (by field_simp; ring)

lemma hFB (x : ℝ) (hx : x ≠ 0) : HasDerivAt FB (6 * Real.cos x * riccatiU2 x * (x ^ 2)⁻¹) x := by
  have := ((Real.hasDerivAt_cos x).mul (hD x hx)).add ((Real.hasDerivAt_sin x).mul (hu2 x hx))
  exact this.congr_deriv (by field_simp; ring)

lemma cwa0 (f a : ℝ → ℝ) (ha : Continuous a) (ha0 : a 0 = 0) (hf : ∀ t, 0 ≤ t → |f t| ≤ a t)
    (S : Set ℝ) (hS : S ⊆ Set.Ici 0) : ContinuousWithinAt f S 0 := by
  have f0 : f 0 = 0 := by have := hf 0 le_rfl; rw [ha0] at this; exact abs_nonpos_iff.1 this
  rw [ContinuousWithinAt, f0]
  apply squeeze_zero_norm' (a := a)
  · exact eventually_nhdsWithin_of_forall (fun t ht => hf t (hS ht))
  · have := ha.tendsto 0; rw [ha0] at this; exact this.mono_left nhdsWithin_le_nhds

lemma meas_u2 : Measurable riccatiU2 := by unfold riccatiU2; fun_prop

lemma intOn (k : ℝ → ℝ) (hk : Measurable k) (C : ℝ) (hb : ∀ t, |k t| ≤ C) (r : ℝ) :
    IntegrableOn (fun t => k t * riccatiU2 t * (t ^ 2)⁻¹) (Set.Ioc 0 r) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  apply Measure.integrableOn_of_bounded (M := C * (r / 15)) measure_Ioc_lt_top.ne
  · exact ((hk.mul meas_u2).mul (by fun_prop)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    have h0 : 0 < t := ht.1
    have hu := u2_bound t h0.le
    have h2 : |riccatiU2 t * (t ^ 2)⁻¹| ≤ r / 15 := by
      rw [abs_mul, abs_inv, abs_of_pos (pow_pos h0 2), ← div_eq_mul_inv, div_le_iff₀ (pow_pos h0 2)]
      nlinarith [ht.2, pow_pos h0 2, show t ^ 3 / 15 = t / 15 * t ^ 2 by ring]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul]
    exact mul_le_mul (hb t) h2 (abs_nonneg _) hC

lemma u2_cont (r : ℝ) : ContinuousOn riccatiU2 (Set.Icc 0 r) := by
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · subst h
    exact cwa0 riccatiU2 (fun t => t ^ 3 / 15) (by fun_prop) (by simp) u2_bound _ (fun x hx => hx.1)
  · exact (hu2 t h.ne').continuousAt.continuousWithinAt

lemma FA_cont (s : ℝ) : ContinuousOn FA (Set.Icc 0 s) := by
  intro t ht
  rcases ht.1.eq_or_lt with h | h
  · subst h
    exact cwa0 FA (fun t => 7 * t ^ 2 / 15 + t ^ 3 / 15) (by fun_prop) (by simp) FA_bound _
      (fun x hx => hx.1)
  · exact (hFA t h.ne').continuousAt.continuousWithinAt

lemma FB_cont (a b : ℝ) (ha : 0 < a) : ContinuousOn FB (Set.Icc a b) := fun t ht =>
  (hFB t (by linarith [ht.1])).continuousAt.continuousWithinAt

lemma ii (k : ℝ → ℝ) (hk : Measurable k) (C : ℝ) (hb : ∀ t, |k t| ≤ C) (r a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbr : b ≤ r) :
    IntervalIntegrable (fun t => k t * riccatiU2 t * (t ^ 2)⁻¹) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (intOn k hk C hb r).mono_set (Set.Ioc_subset_Ioc ha hbr)

lemma FA0 : FA 0 = 0 := by simp [FA, Arxivmath_ph_0108008.riccatiU2]

lemma keyInt (r : ℝ) (hr0 : 0 < r) (s : ℝ) (hs : s ∈ Set.Icc 0 r) :
    ∫ t in (0:ℝ)..r, (6 * Real.sin (min s t) * Real.cos (max s t)) * riccatiU2 t * (t ^ 2)⁻¹
      = -riccatiU2 s + Real.sin s * FB r := by
  have hbd : ∀ s t, |6 * Real.sin (min s t) * Real.cos (max s t)| ≤ 6 := by
    intro s t
    rw [abs_mul, abs_mul]
    have := Real.abs_sin_le_one (min s t); have := Real.abs_cos_le_one (max s t)
    have := abs_nonneg (Real.sin (min s t)); have := abs_nonneg (Real.cos (max s t))
    norm_num; nlinarith
  have hmeas : ∀ s, Measurable (fun t => 6 * Real.sin (min s t) * Real.cos (max s t)) := by
    intro s; fun_prop
  rcases hs.1.eq_or_lt with h0 | hpos
  · subst h0
    have : ∫ t in (0:ℝ)..r, (6 * Real.sin (min 0 t) * Real.cos (max 0 t)) * riccatiU2 t * (t ^ 2)⁻¹
        = ∫ t in (0:ℝ)..r, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hr0.le] at ht
      simp [min_eq_left ht.1]
    rw [this]; simp [Arxivmath_ph_0108008.riccatiU2]
  · have i1 := ii _ (hmeas s) 6 (hbd s) r 0 s le_rfl hpos.le hs.2
    have i2 := ii _ (hmeas s) 6 (hbd s) r s r hpos.le hs.2 le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have e1 : ∫ t in (0:ℝ)..s, (6 * Real.sin (min s t) * Real.cos (max s t)) * riccatiU2 t * (t ^ 2)⁻¹
        = ∫ t in (0:ℝ)..s, Real.cos s * (6 * Real.sin t * riccatiU2 t * (t ^ 2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hpos.le] at ht
      simp only [min_eq_right ht.2, max_eq_left ht.2]; ring
    have e2 : ∫ t in s..r, (6 * Real.sin (min s t) * Real.cos (max s t)) * riccatiU2 t * (t ^ 2)⁻¹
        = ∫ t in s..r, Real.sin s * (6 * Real.cos t * riccatiU2 t * (t ^ 2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hs.2] at ht
      simp only [min_eq_left ht.1, max_eq_right ht.1]; ring
    rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have j1 := ii (fun t => 6 * Real.sin t) (by fun_prop) 6
      (fun t => by rw [abs_mul]; have := Real.abs_sin_le_one t; norm_num; linarith) r 0 s le_rfl hpos.le hs.2
    have j2 := ii (fun t => 6 * Real.cos t) (by fun_prop) 6
      (fun t => by rw [abs_mul]; have := Real.abs_cos_le_one t; norm_num; linarith) r s r hpos.le hs.2 le_rfl
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpos.le (FA_cont s)
        (fun x hx => hFA x hx.1.ne') j1,
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2 (FB_cont s r hpos)
        (fun x hx => hFB x (by linarith [hx.1])) j2, FA0]
    simp only [FA, FB]
    linear_combination (-riccatiU2 s) * Real.sin_sq_add_cos_sq s

lemma wronsk_eq (r : ℝ) (hr : r ≠ 0) : Arxivmath_ph_0108008.wronskP r = -FB r := by
  unfold Arxivmath_ph_0108008.wronskP FB
  rw [(hu2 r hr).deriv, show deriv (fun x => -Real.cos x) r = Real.sin r by simp]
  ring

lemma kerEq (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) (γ : ℝ → ℝ) (hγ : γ 0 = -6) (s t : ℝ) :
    Arxivmath_ph_0108008.ctKernel u v {0} γ s t = 6 * Real.sin (min s t) * Real.cos (max s t) := by
  simp [Arxivmath_ph_0108008.ctKernel, hu, hv, hγ]

lemma solOf (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) (γ : ℝ → ℝ) (hγ : γ 0 = -6) (r : ℝ) (hr0 : 0 < r)
    (hFr : FB r = 0) :
    Arxivmath_ph_0108008.IsCTSolution (Arxivmath_ph_0108008.ctKernel u v {0} γ) r riccatiU2 := by
  have hk' : ∀ s, (fun t => Arxivmath_ph_0108008.ctKernel u v {0} γ s t
      * riccatiU2 t * (t ^ 2)⁻¹) =
      fun t => (6 * Real.sin (min s t) * Real.cos (max s t)) * riccatiU2 t * (t ^ 2)⁻¹ := by
    intro s; funext t; rw [kerEq u v hu hv γ hγ]
  refine ⟨u2_cont r, by simp [Arxivmath_ph_0108008.riccatiU2], fun s hs => ⟨?_, ?_⟩⟩
  · rw [hk' s]
    refine intOn _ (by fun_prop) 6 (fun t => ?_) r
    rw [abs_mul, abs_mul]
    have := Real.abs_sin_le_one (min s t); have := Real.abs_cos_le_one (max s t)
    have := abs_nonneg (Real.sin (min s t)); have := abs_nonneg (Real.cos (max s t))
    norm_num; nlinarith
  · rw [hk' s, keyInt r hr0 s hs, hFr]; ring

lemma gamma6 (γ : ℝ → ℝ) (hγ : Arxivmath_ph_0108008.CTCoeffEq {0} {2} γ) : γ 0 = -6 := by
  have := hγ 2 (by simp)
  simp at this
  norm_num at this
  linarith

lemma M_pos (x : ℝ) (h0 : 0 < x) (h1 : x ≤ Real.pi) : 0 < M x := by
  have hm : StrictMonoOn M (Set.Icc 0 Real.pi) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
      (fun y _ => (hasDerivM y).continuousAt.continuousWithinAt)
      (fun y hy => by
        rw [interior_Icc] at hy
        rw [(hasDerivM y).deriv]
        exact mul_pos hy.1 (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2))
  have := hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0.le, h1⟩ h0
  simpa [M] using this

lemma N_pos (x : ℝ) (h0 : 0 < x) (h1 : x ≤ Real.pi) : 0 < N x := by
  have hm : StrictMonoOn N (Set.Icc 0 Real.pi) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
      (fun y _ => (hasDerivN y).continuousAt.continuousWithinAt)
      (fun y hy => by
        rw [interior_Icc] at hy
        rw [(hasDerivN y).deriv]
        exact mul_pos hy.1 (M_pos y hy.1 hy.2.le))
  have := hm ⟨le_rfl, Real.pi_pos.le⟩ ⟨h0.le, h1⟩ h0
  simpa [N] using this

lemma u2_pos (x : ℝ) (h0 : 0 < x) (h1 : x ≤ Real.pi) : 0 < riccatiU2 x := by
  rw [u2_eq x h0.ne']; exact div_pos (N_pos x h0 h1) (pow_pos h0 2)

end CTX
end

open CTX Arxivmath_ph_0108008 in
theorem solution (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) (γ : ℝ → ℝ) (hγ : CTCoeffEq {0} {2} γ)
    (R : ℝ) (hR : 0 < R) (hpR : wronskP R = 0) :
    IsCTSolution (ctKernel u v {0} γ) R riccatiU2 ∧ ∃ s ∈ Set.Ioo 0 R, riccatiU2 s ≠ 0 := by
  have hFr : FB R = 0 := by rw [wronsk_eq R hR.ne'] at hpR; linarith
  refine ⟨solOf u v hu hv γ (gamma6 γ hγ) R hR hFr, min (R / 2) 1, ⟨by positivity, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  · have := Real.pi_gt_three
    exact (u2_pos _ (by positivity) (le_trans (min_le_right _ _) (by linarith))).ne'
