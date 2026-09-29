-- Prove2me | solution 1 for AlgebraicCurve.RadialRegion.exists_reparam_same_side
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/268cb442-d2f8-5e5b-9e65-4ee84742f351

import Mathlib
import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RadialRegion_exists_reparam_same_side

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

namespace SegmentTransport

theorem arcIcc_eq (R : RadialRegion) (k : Fin R.N) :
    R.arcIcc k = Set.Icc (R.φs k.castSucc) (R.φs k.succ) := rfl

theorem loop_re (R : RadialRegion) (s : ℝ) : (R.loop s).re = R.q.re + R.r s * Real.cos s := by
  show (R.q + (R.r s : ℂ) * Complex.exp ((s : ℂ) * Complex.I)).re = _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem loop_im (R : RadialRegion) (s : ℝ) : (R.loop s).im = R.q.im + R.r s * Real.sin s := by
  show (R.q + (R.r s : ℂ) * Complex.exp ((s : ℂ) * Complex.I)).im = _
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]

noncomputable def vert (x₀ y : ℝ) : ℂ := ⟨x₀, y⟩

noncomputable def horiz (y₀ x : ℝ) : ℂ := ⟨x, y₀⟩

theorem vert_re (x₀ y : ℝ) : (vert x₀ y).re = x₀ := rfl
theorem vert_im (x₀ y : ℝ) : (vert x₀ y).im = y := rfl
theorem horiz_re (y₀ x : ℝ) : (horiz y₀ x).re = x := rfl
theorem horiz_im (y₀ x : ℝ) : (horiz y₀ x).im = y₀ := rfl

theorem vert_injective (x₀ : ℝ) : Function.Injective (vert x₀) := by
  intro y y' hyy'
  have h := congrArg Complex.im hyy'
  rwa [vert_im, vert_im] at h

theorem horiz_injective (y₀ : ℝ) : Function.Injective (horiz y₀) := by
  intro x x' hxx'
  have h := congrArg Complex.re hxx'
  rwa [horiz_re, horiz_re] at h

theorem eq_vert {z : ℂ} {x₀ y : ℝ} (hre : z.re = x₀) (him : z.im = y) : z = vert x₀ y := by
  apply Complex.ext
  · rw [vert_re]
    exact hre
  · rw [vert_im]
    exact him

theorem eq_horiz {z : ℂ} {y₀ x : ℝ} (hre : z.re = x) (him : z.im = y₀) : z = horiz y₀ x := by
  apply Complex.ext
  · rw [horiz_re]
    exact hre
  · rw [horiz_im]
    exact him

theorem comp_anti_of_mono_anti {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictMono g)
    (hf : StrictAntiOn f J) : StrictAntiOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_anti_of_anti_mono {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictAnti g)
    (hf : StrictMonoOn f J) : StrictAntiOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_mono_of_mono_mono {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictMono g)
    (hf : StrictMonoOn f J) : StrictMonoOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem comp_mono_of_anti_anti {g f : ℝ → ℝ} {J : Set ℝ} (hg : StrictAnti g)
    (hf : StrictAntiOn f J) : StrictMonoOn (fun t => g (f t)) J := by
  intro t ht t' ht' htt'
  exact hg (hf ht ht' htt')

theorem tan_lt_tan_shifted {x y : ℝ} (hx : π / 2 < x) (hy : y < 3 * π / 2) (hxy : x < y) :
    Real.tan x < Real.tan y := by
  have hx' : x - π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hy' : y - π ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have h1 : Real.tan (x - π) < Real.tan (y - π) := Real.strictMonoOn_tan hx' hy' (by linarith)
  rwa [Real.tan_sub_pi, Real.tan_sub_pi] at h1

theorem cot_lt_cot {u u' : ℝ} (h0 : 0 < u) (hπ : u' < π) (huu : u < u') :
    Real.cos u' / Real.sin u' < Real.cos u / Real.sin u := by
  have hsu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsu' : 0 < Real.sin u' := Real.sin_pos_of_pos_of_lt_pi (by linarith) hπ
  rw [div_lt_div_iff₀ hsu' hsu]
  have h1 : 0 < Real.sin (u' - u) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_sub] at h1
  nlinarith

theorem cot_sub_pi (t : ℝ) : Real.cos t / Real.sin t = Real.cos (t - π) / Real.sin (t - π) := by
  rw [Real.cos_sub_pi, Real.sin_sub_pi, neg_div_neg_eq]

theorem cot_eq_tan_pi_div_two_sub (x : ℝ) : Real.cos x / Real.sin x = Real.tan (π / 2 - x) := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem cot_pi_div_two_sub (v : ℝ) :
    Real.cos (π / 2 - v) / Real.sin (π / 2 - v) = Real.tan v := by
  rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, ← Real.tan_eq_sin_div_cos]

theorem exists_shift {J : Set ℝ}
    (hJ : J ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ J ⊆ Set.Ioo (3 * π / 2) (5 * π / 2)) :
    ∃ c : ℝ, (∀ s ∈ J, -(π / 2) < s - c ∧ s - c < π / 2) ∧
      (∀ x : ℝ, Real.cos (x - c) = Real.cos x) ∧ (∀ x : ℝ, Real.tan (x - c) = Real.tan x) := by
  rcases hJ with hJ | hJ
  · refine ⟨0, fun s hs => ?_, fun x => by rw [sub_zero], fun x => by rw [sub_zero]⟩
    have h := hJ hs
    have h1 := h.1
    have h2 := h.2
    exact ⟨by linarith, by linarith⟩
  · refine ⟨2 * π, fun s hs => ?_, fun x => Real.cos_sub_two_pi x, fun x => ?_⟩
    · have h := hJ hs
      have h1 := h.1
      have h2 := h.2
      exact ⟨by linarith, by linarith⟩
    · rw [show x - 2 * π = x - π - π by ring, Real.tan_sub_pi, Real.tan_sub_pi]

theorem right_shape (R : RadialRegion) (k : Fin R.N) {a x₀ : ℝ} (ha : 0 < a)
    (hx : R.q.re + a = x₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = vert x₀ (h s)) ∧
      StrictMonoOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ y : ℝ, h (g y) = y) ∧
      StrictMono g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  obtain ⟨c, hwin, hcosc, htanc⟩ := exists_shift hw
  have hmem : ∀ s ∈ R.arcIcc k, s - c ∈ Set.Ioo (-(π / 2)) (π / 2) := fun s hs =>
    ⟨(hwin s hs).1, (hwin s hs).2⟩
  have hcos : ∀ s ∈ R.arcIcc k, 0 < Real.cos s := by
    intro s hs
    rw [← hcosc s]
    exact Real.cos_pos_of_mem_Ioo (hmem s hs)
  refine ⟨fun s => R.q.im + a * Real.tan s, fun y => Real.arctan ((y - R.q.im) / a) + c,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hc : Real.cos s ≠ 0 := (hcos s hs).ne'
    show R.loop s = vert x₀ (R.q.im + a * Real.tan s)
    apply eq_vert
    · rw [loop_re, hr s hs, inv_div, div_mul_cancel₀ _ hc]
      exact hx
    · rw [loop_im, hr s hs, inv_div, Real.tan_eq_sin_div_cos]
      ring
  · intro s hs s' hs' hss'
    have h1 : Real.tan s < Real.tan s' := by
      rw [← htanc s, ← htanc s']
      exact Real.strictMonoOn_tan (hmem s hs) (hmem s' hs') (by linarith)
    have h2 := mul_lt_mul_of_pos_left h1 ha
    show R.q.im + a * Real.tan s < R.q.im + a * Real.tan s'
    linarith
  · refine ContDiffOn.add contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact fun s hs => (Real.contDiffAt_tan.mpr (hcos s hs).ne').contDiffWithinAt
  · intro s hs
    have h1 := (hwin s hs).1
    have h2 := (hwin s hs).2
    have hat : Real.arctan (Real.tan (s - c)) = s - c := Real.arctan_tan h1 h2
    show Real.arctan ((R.q.im + a * Real.tan s - R.q.im) / a) + c = s
    rw [show R.q.im + a * Real.tan s - R.q.im = a * Real.tan s by ring,
      mul_div_cancel_left₀ _ ha.ne', ← htanc s, hat]
    ring
  · intro y
    have ht : Real.tan (Real.arctan ((y - R.q.im) / a) + c) = (y - R.q.im) / a := by
      rw [← htanc (Real.arctan ((y - R.q.im) / a) + c),
        show Real.arctan ((y - R.q.im) / a) + c - c = Real.arctan ((y - R.q.im) / a) by ring,
        Real.tan_arctan]
    show R.q.im + a * Real.tan (Real.arctan ((y - R.q.im) / a) + c) = y
    rw [ht, mul_div_cancel₀ _ ha.ne']
    ring
  · intro y y' hyy'
    have h1 : (y - R.q.im) / a < (y' - R.q.im) / a := div_lt_div_of_pos_right (by linarith) ha
    have h2 := Real.arctan_strictMono h1
    show Real.arctan ((y - R.q.im) / a) + c < Real.arctan ((y' - R.q.im) / a) + c
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (f t - R.q.im) / a) J := by
      refine ContDiffOn.div_const ?_ a
      exact ContDiffOn.sub hf contDiffOn_const
    show ContDiffOn ℝ 1 (fun t => Real.arctan ((f t - R.q.im) / a) + c) J
    refine ContDiffOn.add ?_ contDiffOn_const
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem left_shape (R : RadialRegion) (k : Fin R.N) {b x₀ : ℝ} (hb : 0 < b)
    (hx : R.q.re - b = x₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = vert x₀ (h s)) ∧
      StrictAntiOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ y : ℝ, h (g y) = y) ∧
      StrictAnti g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hcos : ∀ s ∈ R.arcIcc k, Real.cos s < 0 := by
    intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  refine ⟨fun s => R.q.im - b * Real.tan s, fun y => Real.arctan ((R.q.im - y) / b) + π,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hc : Real.cos s ≠ 0 := (hcos s hs).ne
    show R.loop s = vert x₀ (R.q.im - b * Real.tan s)
    apply eq_vert
    · have h1 : b / -Real.cos s * Real.cos s = -b := by
        field_simp
      rw [loop_re, hr s hs, inv_div, h1]
      linarith
    · have h2 : b / -Real.cos s * Real.sin s = -(b * Real.tan s) := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp
      rw [loop_im, hr s hs, inv_div]
      linarith
  · intro s hs s' hs' hss'
    have h1 : Real.tan s < Real.tan s' := tan_lt_tan_shifted (hw hs).1 (hw hs').2 hss'
    have h2 := mul_lt_mul_of_pos_left h1 hb
    show R.q.im - b * Real.tan s' < R.q.im - b * Real.tan s
    linarith
  · refine ContDiffOn.sub contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact fun s hs => (Real.contDiffAt_tan.mpr (hcos s hs).ne).contDiffWithinAt
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (s - π)) = s - π :=
      Real.arctan_tan (by linarith) (by linarith)
    show Real.arctan ((R.q.im - (R.q.im - b * Real.tan s)) / b) + π = s
    rw [show R.q.im - (R.q.im - b * Real.tan s) = b * Real.tan s by ring,
      mul_div_cancel_left₀ _ hb.ne', ← Real.tan_sub_pi s, hat]
    ring
  · intro y
    show R.q.im - b * Real.tan (Real.arctan ((R.q.im - y) / b) + π) = y
    rw [Real.tan_add_pi, Real.tan_arctan, mul_div_cancel₀ _ hb.ne']
    ring
  · intro y y' hyy'
    have h1 : (R.q.im - y') / b < (R.q.im - y) / b := div_lt_div_of_pos_right (by linarith) hb
    have h2 := Real.arctan_strictMono h1
    show Real.arctan ((R.q.im - y') / b) + π < Real.arctan ((R.q.im - y) / b) + π
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (R.q.im - f t) / b) J := by
      refine ContDiffOn.div_const ?_ b
      exact ContDiffOn.sub contDiffOn_const hf
    show ContDiffOn ℝ 1 (fun t => Real.arctan ((R.q.im - f t) / b) + π) J
    refine ContDiffOn.add ?_ contDiffOn_const
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem top_shape (R : RadialRegion) (k : Fin R.N) {c y₀ : ℝ} (hc : 0 < c)
    (hy : R.q.im + c = y₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo 0 π) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = horiz y₀ (h s)) ∧
      StrictAntiOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ x : ℝ, h (g x) = x) ∧
      StrictAnti g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hsin : ∀ s ∈ R.arcIcc k, 0 < Real.sin s := fun s hs =>
    Real.sin_pos_of_pos_of_lt_pi (hw hs).1 (hw hs).2
  refine ⟨fun s => R.q.re + c * (Real.cos s / Real.sin s),
    fun x => π / 2 - Real.arctan ((x - R.q.re) / c), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : Real.sin s ≠ 0 := (hsin s hs).ne'
    show R.loop s = horiz y₀ (R.q.re + c * (Real.cos s / Real.sin s))
    apply eq_horiz
    · rw [loop_re, hr s hs, inv_div]
      ring
    · rw [loop_im, hr s hs, inv_div, div_mul_cancel₀ _ hs0]
      exact hy
  · intro s hs s' hs' hss'
    have h1 : Real.cos s' / Real.sin s' < Real.cos s / Real.sin s :=
      cot_lt_cot (hw hs).1 (hw hs').2 hss'
    have h2 := mul_lt_mul_of_pos_left h1 hc
    show R.q.re + c * (Real.cos s' / Real.sin s') < R.q.re + c * (Real.cos s / Real.sin s)
    linarith
  · refine ContDiffOn.add contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact ContDiffOn.div Real.contDiff_cos.contDiffOn Real.contDiff_sin.contDiffOn
      (fun s hs => (hsin s hs).ne')
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (π / 2 - s)) = π / 2 - s :=
      Real.arctan_tan (by linarith) (by linarith)
    have e : R.q.re + c * (Real.cos s / Real.sin s) - R.q.re = c * (Real.cos s / Real.sin s) := by
      ring
    show π / 2 - Real.arctan ((R.q.re + c * (Real.cos s / Real.sin s) - R.q.re) / c) = s
    rw [e, mul_div_cancel_left₀ _ hc.ne', cot_eq_tan_pi_div_two_sub, hat]
    ring
  · intro x
    show R.q.re + c * (Real.cos (π / 2 - Real.arctan ((x - R.q.re) / c)) /
        Real.sin (π / 2 - Real.arctan ((x - R.q.re) / c))) = x
    rw [cot_pi_div_two_sub, Real.tan_arctan, mul_div_cancel₀ _ hc.ne']
    ring
  · intro x x' hxx'
    have h1 : (x - R.q.re) / c < (x' - R.q.re) / c := div_lt_div_of_pos_right (by linarith) hc
    have h2 := Real.arctan_strictMono h1
    show π / 2 - Real.arctan ((x' - R.q.re) / c) < π / 2 - Real.arctan ((x - R.q.re) / c)
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (f t - R.q.re) / c) J := by
      refine ContDiffOn.div_const ?_ c
      exact ContDiffOn.sub hf contDiffOn_const
    show ContDiffOn ℝ 1 (fun t => π / 2 - Real.arctan ((f t - R.q.re) / c)) J
    refine ContDiffOn.sub contDiffOn_const ?_
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem bottom_shape (R : RadialRegion) (k : Fin R.N) {d y₀ : ℝ} (hd : 0 < d)
    (hy : R.q.im - d = y₀)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo π (2 * π)) :
    ∃ h g : ℝ → ℝ,
      (∀ s ∈ R.arcIcc k, R.loop s = horiz y₀ (h s)) ∧
      StrictMonoOn h (R.arcIcc k) ∧ ContDiffOn ℝ 1 h (R.arcIcc k) ∧
      (∀ s ∈ R.arcIcc k, g (h s) = s) ∧ (∀ x : ℝ, h (g x) = x) ∧
      StrictMono g ∧
      (∀ (f : ℝ → ℝ) (J : Set ℝ), ContDiffOn ℝ 1 f J → ContDiffOn ℝ 1 (fun t => g (f t)) J) := by
  have hsin : ∀ s ∈ R.arcIcc k, Real.sin s < 0 := by
    intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have h3 : 0 < Real.sin (s - π) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h3
    linarith
  refine ⟨fun s => R.q.re - d * (Real.cos s / Real.sin s),
    fun x => π / 2 - Real.arctan ((R.q.re - x) / d) + π, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : Real.sin s ≠ 0 := (hsin s hs).ne
    show R.loop s = horiz y₀ (R.q.re - d * (Real.cos s / Real.sin s))
    apply eq_horiz
    · have h1 : d / -Real.sin s * Real.cos s = -(d * (Real.cos s / Real.sin s)) := by
        field_simp
      rw [loop_re, hr s hs, inv_div]
      linarith
    · have h2 : d / -Real.sin s * Real.sin s = -d := by
        field_simp
      rw [loop_im, hr s hs, inv_div]
      linarith
  · intro s hs s' hs' hss'
    have h1 : Real.cos s' / Real.sin s' < Real.cos s / Real.sin s := by
      have hs1 := (hw hs).1
      have hs2 := (hw hs').2
      rw [cot_sub_pi s, cot_sub_pi s']
      exact cot_lt_cot (by linarith) (by linarith) (by linarith)
    have h2 := mul_lt_mul_of_pos_left h1 hd
    show R.q.re - d * (Real.cos s / Real.sin s) < R.q.re - d * (Real.cos s' / Real.sin s')
    linarith
  · refine ContDiffOn.sub contDiffOn_const ?_
    refine ContDiffOn.mul contDiffOn_const ?_
    exact ContDiffOn.div Real.contDiff_cos.contDiffOn Real.contDiff_sin.contDiffOn
      (fun s hs => (hsin s hs).ne)
  · intro s hs
    have h1 := (hw hs).1
    have h2 := (hw hs).2
    have hat : Real.arctan (Real.tan (π / 2 - (s - π))) = π / 2 - (s - π) :=
      Real.arctan_tan (by linarith) (by linarith)
    have e : R.q.re - (R.q.re - d * (Real.cos s / Real.sin s)) = d * (Real.cos s / Real.sin s) := by
      ring
    show π / 2 - Real.arctan ((R.q.re - (R.q.re - d * (Real.cos s / Real.sin s))) / d) + π = s
    rw [e, mul_div_cancel_left₀ _ hd.ne', cot_sub_pi s, cot_eq_tan_pi_div_two_sub, hat]
    ring
  · intro x
    show R.q.re - d * (Real.cos (π / 2 - Real.arctan ((R.q.re - x) / d) + π) /
        Real.sin (π / 2 - Real.arctan ((R.q.re - x) / d) + π)) = x
    rw [Real.cos_add_pi, Real.sin_add_pi, neg_div_neg_eq, cot_pi_div_two_sub, Real.tan_arctan,
      mul_div_cancel₀ _ hd.ne']
    ring
  · intro x x' hxx'
    have h1 : (R.q.re - x') / d < (R.q.re - x) / d := div_lt_div_of_pos_right (by linarith) hd
    have h2 := Real.arctan_strictMono h1
    show π / 2 - Real.arctan ((R.q.re - x) / d) + π < π / 2 - Real.arctan ((R.q.re - x') / d) + π
    linarith
  · intro f J hf
    have hinner : ContDiffOn ℝ 1 (fun t => (R.q.re - f t) / d) J := by
      refine ContDiffOn.div_const ?_ d
      exact ContDiffOn.sub contDiffOn_const hf
    show ContDiffOn ℝ 1 (fun t => π / 2 - Real.arctan ((R.q.re - f t) / d) + π) J
    refine ContDiffOn.add ?_ contDiffOn_const
    refine ContDiffOn.sub contDiffOn_const ?_
    exact Real.contDiff_arctan.comp_contDiffOn hinner

theorem core_anti {R R' : RadialRegion} {k : Fin R.N} {k' : Fin R'.N} {P : ℝ → ℂ}
    (hP : Function.Injective P) {h h' g : ℝ → ℝ}
    (hL : ∀ s ∈ R.arcIcc k, R.loop s = P (h s))
    (hL' : ∀ t ∈ R'.arcIcc k', R'.loop t = P (h' t))
    (hgh : ∀ s ∈ R.arcIcc k, g (h s) = s) (hhg : ∀ y : ℝ, h (g y) = y)
    (hψ : StrictAntiOn (fun t => g (h' t)) (R'.arcIcc k'))
    (hψC : ContDiffOn ℝ 1 (fun t => g (h' t)) (R'.arcIcc k'))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  have hαβ : R.φs k.castSucc ≤ R.φs k.succ := (R.hmono Fin.castSucc_lt_succ).le
  have hαβ' : R'.φs k'.castSucc ≤ R'.φs k'.succ := (R'.hmono Fin.castSucc_lt_succ).le
  have hα : R.φs k.castSucc ∈ R.arcIcc k := Set.left_mem_Icc.mpr hαβ
  have hβ : R.φs k.succ ∈ R.arcIcc k := Set.right_mem_Icc.mpr hαβ
  have hα' : R'.φs k'.castSucc ∈ R'.arcIcc k' := Set.left_mem_Icc.mpr hαβ'
  have hβ' : R'.φs k'.succ ∈ R'.arcIcc k' := Set.right_mem_Icc.mpr hαβ'
  have e₁ : h' (R'.φs k'.succ) = h (R.φs k.castSucc) := by
    apply hP
    rw [← hL' _ hβ', ← hL _ hα]
    exact h₁.symm
  have e₂ : h' (R'.φs k'.castSucc) = h (R.φs k.succ) := by
    apply hP
    rw [← hL' _ hα', ← hL _ hβ]
    exact h₂.symm
  have hψα : g (h' (R'.φs k'.castSucc)) = R.φs k.succ := by
    rw [e₂, hgh _ hβ]
  have hψβ : g (h' (R'.φs k'.succ)) = R.φs k.castSucc := by
    rw [e₁, hgh _ hα]
  refine ⟨fun t => g (h' t), hψ, hψC, hψα, hψβ, fun t ht => ?_⟩
  have ht' : t ∈ Set.Icc (R'.φs k'.castSucc) (R'.φs k'.succ) := ht
  have hlo : g (h' (R'.φs k'.succ)) ≤ g (h' t) := hψ.antitoneOn ht hβ' ht'.2
  have hhi : g (h' t) ≤ g (h' (R'.φs k'.castSucc)) := hψ.antitoneOn hα' ht ht'.1
  rw [hψβ] at hlo
  rw [hψα] at hhi
  have hmem : g (h' t) ∈ R.arcIcc k := by
    rw [arcIcc_eq]
    exact ⟨hlo, hhi⟩
  show R'.loop t = R.loop (g (h' t))
  rw [hL' t ht, hL _ hmem, hhg]

theorem core_mono {R R' : RadialRegion} {k : Fin R.N} {k' : Fin R'.N} {P : ℝ → ℂ}
    (hP : Function.Injective P) {h h' g : ℝ → ℝ}
    (hL : ∀ s ∈ R.arcIcc k, R.loop s = P (h s))
    (hL' : ∀ t ∈ R'.arcIcc k', R'.loop t = P (h' t))
    (hgh : ∀ s ∈ R.arcIcc k, g (h s) = s) (hhg : ∀ y : ℝ, h (g y) = y)
    (hψ : StrictMonoOn (fun t => g (h' t)) (R'.arcIcc k'))
    (hψC : ContDiffOn ℝ 1 (fun t => g (h' t)) (R'.arcIcc k'))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  have hαβ : R.φs k.castSucc ≤ R.φs k.succ := (R.hmono Fin.castSucc_lt_succ).le
  have hαβ' : R'.φs k'.castSucc ≤ R'.φs k'.succ := (R'.hmono Fin.castSucc_lt_succ).le
  have hα : R.φs k.castSucc ∈ R.arcIcc k := Set.left_mem_Icc.mpr hαβ
  have hβ : R.φs k.succ ∈ R.arcIcc k := Set.right_mem_Icc.mpr hαβ
  have hα' : R'.φs k'.castSucc ∈ R'.arcIcc k' := Set.left_mem_Icc.mpr hαβ'
  have hβ' : R'.φs k'.succ ∈ R'.arcIcc k' := Set.right_mem_Icc.mpr hαβ'
  have e₁ : h' (R'.φs k'.castSucc) = h (R.φs k.castSucc) := by
    apply hP
    rw [← hL' _ hα', ← hL _ hα]
    exact h₁.symm
  have e₂ : h' (R'.φs k'.succ) = h (R.φs k.succ) := by
    apply hP
    rw [← hL' _ hβ', ← hL _ hβ]
    exact h₂.symm
  have hψα : g (h' (R'.φs k'.castSucc)) = R.φs k.castSucc := by
    rw [e₁, hgh _ hα]
  have hψβ : g (h' (R'.φs k'.succ)) = R.φs k.succ := by
    rw [e₂, hgh _ hβ]
  refine ⟨fun t => g (h' t), hψ, hψC, hψα, hψβ, fun t ht => ?_⟩
  have ht' : t ∈ Set.Icc (R'.φs k'.castSucc) (R'.φs k'.succ) := ht
  have hlo : g (h' (R'.φs k'.castSucc)) ≤ g (h' t) := hψ.monotoneOn hα' ht ht'.1
  have hhi : g (h' t) ≤ g (h' (R'.φs k'.succ)) := hψ.monotoneOn ht hβ' ht'.2
  rw [hψα] at hlo
  rw [hψβ] at hhi
  have hmem : g (h' t) ∈ R.arcIcc k := by
    rw [arcIcc_eq]
    exact ⟨hlo, hhi⟩
  show R'.loop t = R.loop (g (h' t))
  rw [hL' t ht, hL _ hmem, hhg]

theorem opposite_vertical (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hline : R.q.re + a = R'.q.re - b)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := right_shape R k ha rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := left_shape R' k' hb hline.symm hr' hw'
  exact core_anti (vert_injective (R.q.re + a)) hl hl' hgh hhg (comp_anti_of_mono_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem opposite_horizontal (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hline : R.q.im + c = R'.q.im - d)
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo 0 π)
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo π (2 * π))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc)) :
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := top_shape R k hc rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := bottom_shape R' k' hd hline.symm hr' hw'
  exact core_anti (horiz_injective (R.q.im + c)) hl hl' hgh hhg (comp_anti_of_anti_mono hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_right (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ)
    (ha : 0 < a) (ha' : 0 < a') (hline : R.q.re + a = R'.q.re + a')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
      R'.arcIcc k' ⊆ Set.Ioo (3 * π / 2) (5 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := right_shape R k ha rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := right_shape R' k' ha' hline.symm hr' hw'
  exact core_mono (vert_injective (R.q.re + a)) hl hl' hgh hhg (comp_mono_of_mono_mono hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_left (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ)
    (hb : 0 < b) (hb' : 0 < b') (hline : R.q.re - b = R'.q.re - b')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹)
    (hw : R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo (π / 2) (3 * π / 2))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := left_shape R k hb rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := left_shape R' k' hb' hline.symm hr' hw'
  exact core_mono (vert_injective (R.q.re - b)) hl hl' hgh hhg (comp_mono_of_anti_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_top (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ)
    (hc : 0 < c) (hc' : 0 < c') (hline : R.q.im + c = R'.q.im + c')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo 0 π)
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) (hw' : R'.arcIcc k' ⊆ Set.Ioo 0 π)
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := top_shape R k hc rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := top_shape R' k' hc' hline.symm hr' hw'
  exact core_mono (horiz_injective (R.q.im + c)) hl hl' hgh hhg (comp_mono_of_anti_anti hg hm')
    (hgC h' _ hC') h₁ h₂

theorem same_bottom (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ)
    (hd : 0 < d) (hd' : 0 < d') (hline : R.q.im - d = R'.q.im - d')
    (hr : ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) (hw : R.arcIcc k ⊆ Set.Ioo π (2 * π))
    (hr' : ∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹)
    (hw' : R'.arcIcc k' ⊆ Set.Ioo π (2 * π))
    (h₁ : R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc))
    (h₂ : R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ)) :
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
      ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
      ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t) := by
  obtain ⟨h, g, hl, -, -, hgh, hhg, hg, hgC⟩ := bottom_shape R k hd rfl hr hw
  obtain ⟨h', _, hl', hm', hC', -, -, -, -⟩ := bottom_shape R' k' hd' hline.symm hr' hw'
  exact core_mono (horiz_injective (R.q.im - d)) hl hl' hgh hhg (comp_mono_of_mono_mono hg hm')
    (hgC h' _ hC') h₁ h₂

theorem anti_affine_pos {L : ℝ → ℂ} {g : ℝ → ℂ} {α β α' β' m c₀ : ℝ} {J : Set ℝ} {u v : ℝ}
    (hJ : J = Set.Icc u v) (huv : u < v) (hm : 0 < m) (hα : m * α' + c₀ = α) (hβ : m * β' + c₀ = β)
    (h : ∃ ψ : ℝ → ℝ, StrictAntiOn ψ J ∧ ContDiffOn ℝ 1 ψ J ∧ ψ u = β ∧ ψ v = α ∧ ∀ t ∈ J, g t = L (ψ t)) :
    ∃ ψ' : ℝ → ℝ, StrictAntiOn ψ' J ∧ ContDiffOn ℝ 1 ψ' J ∧ ψ' u = β' ∧ ψ' v = α' ∧
      ∀ t ∈ J, g t = L (m * ψ' t + c₀) := by
  have _ := hJ
  have _ := huv
  obtain ⟨ψ, hanti, hC, hu, hv, hL⟩ := h
  have key : ∀ t : ℝ, m * ((ψ t - c₀) / m) + c₀ = ψ t := by
    intro t
    rw [mul_div_cancel₀ _ hm.ne']
    ring
  refine ⟨fun t => (ψ t - c₀) / m, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht t' ht' htt'
    have h1 := hanti ht ht' htt'
    show (ψ t' - c₀) / m < (ψ t - c₀) / m
    apply div_lt_div_of_pos_right ?_ hm
    linarith
  · refine ContDiffOn.div_const ?_ m
    exact ContDiffOn.sub hC contDiffOn_const
  · show (ψ u - c₀) / m = β'
    rw [hu, show β - c₀ = m * β' by linarith, mul_div_cancel_left₀ _ hm.ne']
  · show (ψ v - c₀) / m = α'
    rw [hv, show α - c₀ = m * α' by linarith, mul_div_cancel_left₀ _ hm.ne']
  · intro t ht
    show g t = L (m * ((ψ t - c₀) / m) + c₀)
    rw [key]
    exact hL t ht

theorem anti_of_mono_affine_neg {L : ℝ → ℂ} {g : ℝ → ℂ} {α β α' β' m c₀ : ℝ} {J : Set ℝ} {u v : ℝ}
    (hJ : J = Set.Icc u v) (huv : u < v) (hm : m < 0) (hα : m * α' + c₀ = β) (hβ : m * β' + c₀ = α)
    (h : ∃ ψ : ℝ → ℝ, StrictMonoOn ψ J ∧ ContDiffOn ℝ 1 ψ J ∧ ψ u = α ∧ ψ v = β ∧ ∀ t ∈ J, g t = L (ψ t)) :
    ∃ ψ' : ℝ → ℝ, StrictAntiOn ψ' J ∧ ContDiffOn ℝ 1 ψ' J ∧ ψ' u = β' ∧ ψ' v = α' ∧
      ∀ t ∈ J, g t = L (m * ψ' t + c₀) := by
  have _ := hJ
  have _ := huv
  obtain ⟨ψ, hmono, hC, hu, hv, hL⟩ := h
  have hm' : 0 < -m := by linarith
  have key : ∀ t : ℝ, m * ((c₀ - ψ t) / -m) + c₀ = ψ t := by
    intro t
    have e : -m * ((c₀ - ψ t) / -m) = c₀ - ψ t := mul_div_cancel₀ _ hm'.ne'
    linarith
  refine ⟨fun t => (c₀ - ψ t) / -m, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht t' ht' htt'
    have h1 := hmono ht ht' htt'
    show (c₀ - ψ t') / -m < (c₀ - ψ t) / -m
    apply div_lt_div_of_pos_right ?_ hm'
    linarith
  · refine ContDiffOn.div_const ?_ (-m)
    exact ContDiffOn.sub contDiffOn_const hC
  · show (c₀ - ψ u) / -m = β'
    rw [hu, show c₀ - α = -m * β' by linarith, mul_div_cancel_left₀ _ hm'.ne']
  · show (c₀ - ψ v) / -m = α'
    rw [hv, show c₀ - β = -m * α' by linarith, mul_div_cancel_left₀ _ hm'.ne']
  · intro t ht
    show g t = L (m * ((c₀ - ψ t) / -m) + c₀)
    rw [key]
    exact hL t ht

end SegmentTransport

namespace SegmentReparam

theorem exists_reparam_across_edge :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ), 0 < a → 0 < b →
      R.q.re + a = R'.q.re - b →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹) →
      R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ), 0 < c → 0 < d →
      R.q.im + c = R'.q.im - d →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  refine ⟨?_, ?_⟩
  · intro R R' k k' a b ha hb hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.opposite_vertical R R' k k' a b ha hb hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' c d hc hd hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.opposite_horizontal R R' k k' c d hc hd hline hr hw hr' hw' h₁ h₂

theorem exists_reparam_same_side :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
      R.q.re + a = R'.q.re + a' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
      (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
      R.q.re - b = R'.q.re - b' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
      R.q.im + c = R'.q.im + c' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
      R.q.im - d = R'.q.im - d' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R R' k k' a a' ha ha' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_right R R' k k' a a' ha ha' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' b b' hb hb' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_left R R' k k' b b' hb hb' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' c c' hc hc' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_top R R' k k' c c' hc hc' hline hr hw hr' hw' h₁ h₂
  · intro R R' k k' d d' hd hd' hline hr hw hr' hw' h₁ h₂
    exact SegmentTransport.same_bottom R R' k k' d d' hd hd' hline hr hw hr' hw' h₁ h₂

end SegmentReparam

theorem solution :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
      R.q.re + a = R'.q.re + a' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
      (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
      R.q.re - b = R'.q.re - b' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
      R.q.im + c = R'.q.im + c' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
      R.q.im - d = R'.q.im - d' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by
  exact SegmentReparam.exists_reparam_same_side

end S_AlgebraicCurve_RadialRegion_exists_reparam_same_side
end P2MW
export P2MW.S_AlgebraicCurve_RadialRegion_exists_reparam_same_side (solution)
