-- Prove2me | solution 1 for Arxivmath_ph_0108008.ct_reduction_to_riccati_ode
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T07:46:55.349212+00:00
-- url     : https://prove2.me/submissions/2eceae72-9da9-4ca8-be56-f31dc9aee705

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

lemma d2 (t : ℝ) (ht : t ≠ 0) :
    deriv (deriv riccatiU2) t = 6 * riccatiU2 t / t ^ 2 - riccatiU2 t := by
  have hev : deriv riccatiU2 =ᶠ[𝓝 t] D :=
    (eventually_ne_nhds ht).mono fun y hy => (hu2 y hy).deriv
  exact hev.deriv_eq.trans (hD t ht).deriv

lemma gI (r s : ℝ) : ∫ t in (0:ℝ)..r, Arxivmath_ph_0108008.greenG0 s t * (6 * riccatiU2 t * (t ^ 2)⁻¹)
    = -∫ t in (0:ℝ)..r, (6 * Real.sin (min s t) * Real.cos (max s t)) * riccatiU2 t * (t ^ 2)⁻¹ := by
  rw [← intervalIntegral.integral_neg]
  congr 1; funext t; simp only [Arxivmath_ph_0108008.greenG0]; ring

def v2 (x : ℝ) : ℝ := (3 / x ^ 2 - 1) * Real.cos x + 3 / x * Real.sin x
def Dv (x : ℝ) : ℝ := (-6 / x ^ 3 + 3 / x) * Real.cos x + (3 / x ^ 2 - 1) * (-Real.sin x) - 3 / x ^ 2 * Real.sin x

lemma hv2 (x : ℝ) (hx : x ≠ 0) : HasDerivAt v2 (Dv x) x := by
  have := ((((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)).sub_const 1).mul
    (Real.hasDerivAt_cos x)).add
    (((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_id' x) hx).mul (Real.hasDerivAt_sin x))
  exact this.congr_deriv (by simp only [Pi.div_apply]; unfold Dv; field_simp; ring)

lemma hDv (x : ℝ) (hx : x ≠ 0) : HasDerivAt Dv (6 * v2 x / x ^ 2 - v2 x) x := by
  have := ((((((hasDerivAt_const x (-6:ℝ)).div (hasDerivAt_pow 3 x) (pow_ne_zero 3 hx)).add
    ((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_id' x) hx)).mul (Real.hasDerivAt_cos x)).add
    ((((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)).sub_const 1).mul
      ((Real.hasDerivAt_sin x).neg))).sub
    (((hasDerivAt_const x (3:ℝ)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)).mul (Real.hasDerivAt_sin x)))
  exact this.congr_deriv (by simp only [Pi.div_apply, Pi.add_apply, Pi.neg_apply]; unfold v2; field_simp; ring)

lemma wr_uv (x : ℝ) (hx : x ≠ 0) : riccatiU2 x * Dv x - D x * v2 x = -1 := by
  unfold Arxivmath_ph_0108008.riccatiU2 Dv D v2
  field_simp
  linear_combination (-(x ^ 5)) * Real.sin_sq_add_cos_sq x

lemma wr_const (r : ℝ) (h : ℝ → ℝ)
    (hode : ∀ s ∈ Set.Ioo 0 r, DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
      deriv (deriv h) s + h s = 6 * h s / s ^ 2)
    (w Dw : ℝ → ℝ) (hw : ∀ x, x ≠ 0 → HasDerivAt w (Dw x) x)
    (hDw : ∀ x, x ≠ 0 → HasDerivAt Dw (6 * w x / x ^ 2 - w x) x) :
    ∀ a ∈ Set.Ioo 0 r, ∀ b ∈ Set.Ioo 0 r,
      h a * Dw a - deriv h a * w a = h b * Dw b - deriv h b * w b := by
  have hd : ∀ x ∈ Set.Ioo 0 r, HasDerivAt (fun t => h t * Dw t - deriv h t * w t) 0 x := by
    intro x hx
    obtain ⟨d1, d2, d3⟩ := hode x hx
    have := (d1.hasDerivAt.mul (hDw x hx.1.ne')).sub (d2.hasDerivAt.mul (hw x hx.1.ne'))
    refine this.congr_deriv ?_
    have hx0 : x ≠ 0 := hx.1.ne'
    have e : deriv (deriv h) x = 6 * h x / x ^ 2 - h x := by linarith
    rw [e]; ring
  have key : ∀ a ∈ Set.Ioo 0 r, ∀ b ∈ Set.Ioo 0 r, a ≤ b →
      h b * Dw b - deriv h b * w b = h a * Dw a - deriv h a * w a := by
    intro a ha b hb hab
    have sub : Set.Icc a b ⊆ Set.Ioo 0 r := fun x hx => ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
    exact constant_of_has_deriv_right_zero
      (fun x hx => (hd x (sub hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (sub (Set.Ico_subset_Icc_self hx))).hasDerivWithinAt) b ⟨hab, le_rfl⟩
  intro a ha b hb
  rcases le_total a b with hab | hab
  · exact (key a ha b hb hab).symm
  · exact key b hb a ha hab

lemma blowup (r : ℝ) (hr : 0 < r) (h : ℝ → ℝ)
    (hdiff : ∀ s ∈ Set.Ioo 0 r, DifferentiableAt ℝ h s)
    (h0 : Filter.Tendsto h (𝓝[>] 0) (𝓝 0)) (A : ℝ) (hA : 0 < A)
    (hW : ∀ s ∈ Set.Ioo 0 r, h s * D s - deriv h s * riccatiU2 s = A) : False := by
  obtain ⟨δ1, hδ1, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.1
    (h0 (Metric.ball_mem_nhds 0 one_pos)))
  set δ := min (min δ1 r) (min 1 A) with hδ
  have hδpos : 0 < δ := lt_min (lt_min hδ1 hr) (lt_min one_pos hA)
  have hδ1' : δ ≤ δ1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδr : δ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ1'' : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδA : δ ≤ A := le_trans (min_le_right _ _) (min_le_right _ _)
  have hpi := Real.pi_gt_three
  -- derivative bound
  have hder : ∀ t ∈ Set.Ioo 0 δ, deriv h t ≤ -(15 * A / 2) / t ^ 3 := by
    intro t ht
    have htr : t ∈ Set.Ioo 0 r := ⟨ht.1, lt_of_lt_of_le ht.2 hδr⟩
    have hh1 : |h t| < 1 := by
      have := hsub ⟨ht.1, lt_of_lt_of_le ht.2 hδ1'⟩
      simpa [Real.dist_eq] using this
    have hu := u2_pos t ht.1 (by linarith [ht.2, hδ1''])
    have hub := u2_bound t ht.1.le
    have hDb := D_bound t ht.1
    have hW' := hW t htr
    have hhD : h t * D t ≤ A / 2 := by
      have : |h t * D t| ≤ 7 * t ^ 2 / 15 := by
        rw [abs_mul]
        calc |h t| * |D t| ≤ 1 * |D t| := by gcongr
          _ ≤ 7 * t ^ 2 / 15 := by linarith
      have ht2 : t ^ 2 ≤ A := by nlinarith [ht.1, ht.2, hδ1'', hδA]
      linarith [le_abs_self (h t * D t)]
    have h1 : deriv h t * riccatiU2 t ≤ -(A / 2) := by linarith
    have t3 : 0 < t ^ 3 := pow_pos ht.1 3
    rw [le_div_iff₀ t3]
    have hneg : deriv h t ≤ 0 := by
      by_contra hc; push_neg at hc
      have := mul_pos hc hu; linarith
    have hu' : riccatiU2 t ≤ t ^ 3 / 15 := le_trans (le_abs_self _) hub
    have := mul_le_mul_of_nonpos_left hu' hneg
    linarith
  -- Φ antitone
  have hanti : AntitoneOn (fun t => h t - 3 * A / t ^ 2) (Set.Ioo 0 δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ)
    · intro t ht
      exact ((hdiff t ⟨ht.1, lt_of_lt_of_le ht.2 hδr⟩).continuousAt.sub
        (by fun_prop (disch := exact (pow_pos ht.1 2).ne'))).continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      exact ((hdiff t ⟨ht.1, lt_of_lt_of_le ht.2 hδr⟩).sub
        (by fun_prop (disch := exact (pow_pos ht.1 2).ne'))).differentiableWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      have hd := ((hdiff t ⟨ht.1, lt_of_lt_of_le ht.2 hδr⟩).hasDerivAt.sub
        (((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht.1.ne')).const_mul (3 * A)))
      have e : (fun t => h t - 3 * A / t ^ 2) =
          (h - fun y => 3 * A * (fun x => x ^ 2)⁻¹ y) := by
        funext y; simp [div_eq_mul_inv]
      rw [e, hd.deriv]
      have hx := hder t ht
      have t3 : 0 < t ^ 3 := pow_pos ht.1 3
      have hneg : -(15 * A / 2) / t ^ 3 + 6 * A / t ^ 3 ≤ 0 := by
        rw [← add_div]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) t3.le
      have e2 : deriv h t - 3 * A * (-(((2:ℕ):ℝ) * t ^ (2 - 1)) / (t ^ 2) ^ 2) =
          deriv h t + 6 * A / t ^ 3 := by
        have := ht.1.ne'
        field_simp; ring
      rw [e2]; linarith
  set c := h (δ / 2) - 3 * A / (δ / 2) ^ 2
  -- small t with h t < 1 and 3A/t^2 > 1 - c
  have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), h t < 1 := h0 (Iio_mem_nhds one_pos)
  have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < δ / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (by positivity))
  have hev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
  have hev4 : ∀ᶠ t in 𝓝[>] (0:ℝ), 1 - c < 3 * A / t ^ 2 := by
    have : Filter.Tendsto (fun t : ℝ => 3 * A / t ^ 2) (𝓝[>] 0) Filter.atTop := by
      have h1 : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have := (((continuous_pow 2).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))); simpa using this
        · filter_upwards [self_mem_nhdsWithin] with t ht; exact pow_pos (Set.mem_Ioi.1 ht) 2
      have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop (show (0:ℝ) < 3 * A by positivity)
      refine h2.congr (fun t => ?_)
      simp only [Function.comp_apply, div_eq_mul_inv]
    exact this.eventually_gt_atTop _
  obtain ⟨t, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  have := hanti ⟨h3, by linarith⟩ ⟨by positivity, by linarith⟩ h2.le
  simp only at this
  linarith

lemma uniq (r : ℝ) (hr : 0 < r) (h : ℝ → ℝ)
    (hode : ∀ s ∈ Set.Ioo 0 r, DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
      deriv (deriv h) s + h s = 6 * h s / s ^ 2)
    (h0 : Filter.Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∃ c : ℝ, ∀ s ∈ Set.Ioo 0 r, h s = c * riccatiU2 s := by
  have hm : r / 2 ∈ Set.Ioo 0 r := ⟨by positivity, by linarith⟩
  have Wu := wr_const r h hode riccatiU2 D hu2 hD
  have Wv := wr_const r h hode v2 Dv hv2 hDv
  set A := h (r / 2) * D (r / 2) - deriv h (r / 2) * riccatiU2 (r / 2)
  have hA0 : A = 0 := by
    rcases lt_trichotomy A 0 with hA | hA | hA
    · exfalso
      refine blowup r hr (fun x => -h x) (fun s hs => (hode s hs).1.neg) (by simpa using h0.neg)
        (-A) (by linarith) (fun s hs => ?_)
      rw [show deriv (fun x => -h x) s = -deriv h s from deriv.neg]
      have := Wu s hs (r / 2) hm
      linarith
    · exact hA
    · exfalso
      exact blowup r hr h (fun s hs => (hode s hs).1) h0 A hA (fun s hs => Wu s hs (r / 2) hm)
  refine ⟨-(h (r / 2) * Dv (r / 2) - deriv h (r / 2) * v2 (r / 2)), fun s hs => ?_⟩
  have e1 := Wu s hs (r / 2) hm
  have e2 := Wv s hs (r / 2) hm
  have w := wr_uv s hs.1.ne'
  have e1' : h s * D s - deriv h s * riccatiU2 s = 0 := by rw [e1]; exact hA0
  linear_combination (-(riccatiU2 s)) * e2 + (v2 s) * e1' + (h s) * w

lemma green2 (r : ℝ) (f : ℝ → ℝ)
    (hsin : IntervalIntegrable (fun t => Real.sin t * f t) volume 0 r)
    (hcont : ContinuousOn f (Set.Ioc 0 r)) (s : ℝ) (hs : s ∈ Set.Ioo 0 r) :
    DifferentiableAt ℝ (fun x => ∫ t in (0 : ℝ)..r, Arxivmath_ph_0108008.greenG0 x t * f t) s ∧
    DifferentiableAt ℝ (deriv (fun x => ∫ t in (0 : ℝ)..r, Arxivmath_ph_0108008.greenG0 x t * f t)) s ∧
    deriv (deriv (fun x => ∫ t in (0 : ℝ)..r, Arxivmath_ph_0108008.greenG0 x t * f t)) s +
      (∫ t in (0 : ℝ)..r, Arxivmath_ph_0108008.greenG0 s t * f t) = f s := by
  set w := fun x => ∫ t in (0 : ℝ)..r, Arxivmath_ph_0108008.greenG0 x t * f t
  set P := fun x => ∫ t in (0 : ℝ)..x, Real.sin t * f t
  set Q := fun x => ∫ t in x..r, Real.cos t * f t
  have hO : IsOpen (Set.Ioo (0:ℝ) r) := isOpen_Ioo
  have hcO : ContinuousOn f (Set.Ioo 0 r) := hcont.mono Set.Ioo_subset_Ioc_self
  have hsinI : ∀ x ∈ Set.Ioo 0 r, IntervalIntegrable (fun t => Real.sin t * f t) volume 0 x :=
    fun x hx => hsin.mono_set (Set.uIcc_subset_uIcc (Set.left_mem_uIcc) (by
      rw [Set.uIcc_of_le (by linarith [hx.1, hx.2] : (0:ℝ) ≤ r)]
      exact ⟨hx.1.le, hx.2.le⟩))
  have hcosI : ∀ x ∈ Set.Ioo 0 r, IntervalIntegrable (fun t => Real.cos t * f t) volume x r := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx.2.le]
    exact (Real.continuous_cos.continuousOn).mul (hcont.mono (fun t ht => ⟨by linarith [hx.1, ht.1], ht.2⟩))
  have hrep : ∀ x ∈ Set.Ioo 0 r, w x = -Real.cos x * P x - Real.sin x * Q x := by
    intro x hx
    have i1 : IntervalIntegrable (fun t => Arxivmath_ph_0108008.greenG0 x t * f t) volume 0 x := by
      refine ((hsinI x hx).const_mul (-Real.cos x)).congr ?_
      intro t ht
      rw [Set.uIoc_of_le hx.1.le] at ht
      simp only [Arxivmath_ph_0108008.greenG0, min_eq_right ht.2, max_eq_left ht.2]; ring
    have i2 : IntervalIntegrable (fun t => Arxivmath_ph_0108008.greenG0 x t * f t) volume x r := by
      refine ((hcosI x hx).const_mul (-Real.sin x)).congr ?_
      intro t ht
      rw [Set.uIoc_of_le hx.2.le] at ht
      simp only [Arxivmath_ph_0108008.greenG0, min_eq_left ht.1.le, max_eq_right ht.1.le]; ring
    simp only [w, P, Q]
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    have e1 : ∫ t in (0:ℝ)..x, Arxivmath_ph_0108008.greenG0 x t * f t
        = ∫ t in (0:ℝ)..x, -Real.cos x * (Real.sin t * f t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx.1.le] at ht
      simp only [Arxivmath_ph_0108008.greenG0, min_eq_right ht.2, max_eq_left ht.2]; ring
    have e2 : ∫ t in x..r, Arxivmath_ph_0108008.greenG0 x t * f t
        = ∫ t in x..r, -Real.sin x * (Real.cos t * f t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx.2.le] at ht
      simp only [Arxivmath_ph_0108008.greenG0, min_eq_left ht.1, max_eq_right ht.1]; ring
    rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; ring
  have hP : ∀ x ∈ Set.Ioo 0 r, HasDerivAt P (Real.sin x * f x) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right (hsinI x hx)
      (ContinuousOn.stronglyMeasurableAtFilter hO
        ((Real.continuous_sin.continuousOn).mul hcO) x hx)
      ((Real.continuous_sin.continuousAt).mul (hcO.continuousAt (hO.mem_nhds hx)))
  have hQ : ∀ x ∈ Set.Ioo 0 r, HasDerivAt Q (-(Real.cos x * f x)) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_left (hcosI x hx)
      (ContinuousOn.stronglyMeasurableAtFilter hO
        ((Real.continuous_cos.continuousOn).mul hcO) x hx)
      ((Real.continuous_cos.continuousAt).mul (hcO.continuousAt (hO.mem_nhds hx)))
  set w1 := fun x => Real.sin x * P x - Real.cos x * Q x
  have hw : ∀ x ∈ Set.Ioo 0 r, HasDerivAt w (w1 x) x := by
    intro x hx
    have hev : (fun x => -Real.cos x * P x - Real.sin x * Q x) =ᶠ[𝓝 x] w :=
      Filter.eventually_of_mem (hO.mem_nhds hx) (fun y hy => (hrep y hy).symm)
    have := (((Real.hasDerivAt_cos x).neg.mul (hP x hx)).sub ((Real.hasDerivAt_sin x).mul (hQ x hx)))
    exact (this.congr_of_eventuallyEq hev.symm).congr_deriv (by simp only [w1, Pi.neg_apply]; ring)
  have hw1 : HasDerivAt w1 (Real.cos s * P s + Real.sin s * Q s + f s) s := by
    have := (((Real.hasDerivAt_sin s).mul (hP s hs)).sub ((Real.hasDerivAt_cos s).mul (hQ s hs)))
    exact this.congr_deriv (by
      have := Real.sin_sq_add_cos_sq s
      linear_combination (f s) * this)
  have hdw : deriv w =ᶠ[𝓝 s] w1 :=
    Filter.eventually_of_mem (hO.mem_nhds hs) (fun y hy => (hw y hy).deriv)
  refine ⟨(hw s hs).differentiableAt, (hw1.congr_of_eventuallyEq hdw).differentiableAt, ?_⟩
  rw [(hw1.congr_of_eventuallyEq hdw).deriv]
  change _ + w s = _
  rw [hrep s hs]; ring

end CTX
end

open CTX Arxivmath_ph_0108008 Filter Topology in
theorem solution (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) :
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ ↔ γ 0 = -6) ∧
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ → ∀ s t : ℝ, ctKernel u v {0} γ s t = -6 * greenG0 s t) ∧
    (∀ r : ℝ, 0 < r → ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 r) → ∀ s ∈ Set.Ioo 0 r,
      DifferentiableAt ℝ (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t) s ∧
      DifferentiableAt ℝ (deriv (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t)) s ∧
      deriv (deriv (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t)) s +
        (∫ t in (0 : ℝ)..r, greenG0 s t * f t) = f s) ∧
    (∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ → ∀ r : ℝ, 0 < r → ∀ h : ℝ → ℝ,
      IsCTSolution (ctKernel u v {0} γ) r h → ∀ s ∈ Set.Ioo 0 r,
        DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
        deriv (deriv h) s + h s = 6 * h s / s ^ 2) ∧
    (∀ s : ℝ, 0 < s → deriv (deriv riccatiU2) s + riccatiU2 s = 6 * riccatiU2 s / s ^ 2) ∧
    Tendsto riccatiU2 (𝓝[>] 0) (𝓝 0) ∧ (∃ s : ℝ, 0 < s ∧ riccatiU2 s ≠ 0) ∧
    (∀ r : ℝ, 0 < r → ∀ h : ℝ → ℝ,
      (∀ s ∈ Set.Ioo 0 r, DifferentiableAt ℝ h s ∧ DifferentiableAt ℝ (deriv h) s ∧
        deriv (deriv h) s + h s = 6 * h s / s ^ 2) →
      Tendsto h (𝓝[>] 0) (𝓝 0) → ∃ c : ℝ, ∀ s ∈ Set.Ioo 0 r, h s = c * riccatiU2 s) := by
  have hpi := Real.pi_gt_three
  have kerG : ∀ γ : ℝ → ℝ, CTCoeffEq {0} {2} γ → ∀ s t : ℝ, ctKernel u v {0} γ s t = -6 * greenG0 s t := by
    intro γ hγ s t
    rw [kerEq u v hu hv γ (gamma6 γ hγ)]; simp only [greenG0]; ring
  refine ⟨fun γ => ⟨gamma6 γ, fun h6 l hl => ?_⟩, kerG, ?_, ?_, ?_, ?_, ?_, fun r hr h hode h0 => uniq r hr h hode h0⟩
  · simp at hl; subst hl; simp [h6]; norm_num
  · intro r hr f hf s hs
    refine green2 r f ?_ (hf.mono Set.Ioc_subset_Icc_self) s hs
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hr.le]
    exact (Real.continuous_sin.continuousOn).mul hf
  · intro γ hγ r hr h hsol s hs
    set f := fun t => 6 * h t * (t ^ 2)⁻¹
    obtain ⟨hcont, _, hsol2⟩ := hsol
    have hfc : ContinuousOn f (Set.Ioc 0 r) := by
      refine ((continuousOn_const.mul (hcont.mono Set.Ioc_subset_Icc_self))).mul ?_
      exact ((continuous_pow 2).continuousOn).inv₀ (fun t ht => pow_ne_zero 2 ht.1.ne')
    obtain ⟨s0, hs0def⟩ : ∃ s0 : ℝ, s0 = min r 1 / 2 := ⟨_, rfl⟩
    have hm1 := min_le_left r 1
    have hm2 := min_le_right r 1
    have hm3 : 0 < min r 1 := lt_min hr one_pos
    have hs0 : 0 < s0 := by rw [hs0def]; linarith
    have hs0r : s0 < r := by rw [hs0def]; linarith
    have hs01 : s0 < 1 := by rw [hs0def]; linarith
    have hcs0 : 0 < Real.cos s0 := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsin : IntervalIntegrable (fun t => Real.sin t * f t) volume 0 r := by
      have i1 : IntervalIntegrable (fun t => Real.sin t * f t) volume 0 s0 := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0.le]
        have := ((hsol2 s0 ⟨hs0.le, hs0r.le⟩).1.mono_set (Set.Ioc_subset_Ioc le_rfl hs0r.le)).div_const
          (Real.cos s0)
        refine MeasureTheory.IntegrableOn.congr_fun (show IntegrableOn (fun x => ctKernel u v {0} γ s0 x * h x * (x ^ 2)⁻¹ / Real.cos s0) (Set.Ioc 0 s0) volume from this)
          (fun t ht => ?_) measurableSet_Ioc
        simp only [f]
        rw [kerG γ hγ s0 t]
        simp only [greenG0, min_eq_right ht.2, max_eq_left ht.2]
        rw [div_eq_iff hcs0.ne']
        ring
      have i2 : IntervalIntegrable (fun t => Real.sin t * f t) volume s0 r := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hs0r.le]
        exact (Real.continuous_sin.continuousOn).mul (hfc.mono (fun t ht => ⟨by linarith [ht.1], ht.2⟩))
      exact i1.trans i2
    obtain ⟨d1, d2, d3⟩ := green2 r f hsin hfc s hs
    have hev : h =ᶠ[𝓝 s] (fun x => ∫ t in (0 : ℝ)..r, greenG0 x t * f t) := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hs) (fun x hx => ?_)
      rw [(hsol2 x ⟨hx.1.le, hx.2.le⟩).2, ← intervalIntegral.integral_neg]
      congr 1; funext t; rw [kerG γ hγ x t]; simp only [f]; ring
    refine ⟨d1.congr_of_eventuallyEq hev, d2.congr_of_eventuallyEq hev.deriv, ?_⟩
    rw [hev.deriv.deriv_eq]
    nth_rw 1 [hev.eq_of_nhds]
    rw [d3]
    simp only [f]; ring
  · intro s hs; rw [d2 s hs.ne']; ring
  · apply squeeze_zero_norm' (a := fun t => t ^ 3 / 15)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact u2_bound t (Set.mem_Ioi.1 ht).le
    · have := ((continuous_pow 3).div_const (15:ℝ)).tendsto 0
      simp at this
      exact this.mono_left nhdsWithin_le_nhds
  · exact ⟨1, one_pos, (u2_pos 1 one_pos (by linarith)).ne'⟩
