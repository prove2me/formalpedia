-- Prove2me | solution 1 for AutomorphicForm.ArchWeightOne.intervalIntegral_exp_neg_mul_translate_rotation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5a1c38d3-d1c4-55bd-8c94-decbd19053f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped Manifold Topology ComplexConjugate
open Complex Filter Metric Set MeasureTheory

noncomputable section

namespace Q1WtOneProj

abbrev S (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1]
    (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)

abbrev R (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
    (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
        exact one_ne_zero)

private abbrev _root_.Q1WtOneProj.rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
    (by rw [Matrix.det_fin_two_of, show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ
          = Real.cos θ ^ 2 + Real.sin θ ^ 2 by ring, Real.cos_sq_add_sin_sq]
        exact one_ne_zero)

p2m_export "Q1WtOneProj" "rot"
theorem rot_eq_R (θ : ℝ) : rot θ = R (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ) := rfl

abbrev eps : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp [Matrix.det_fin_two_of])

def coeffC (h : GL (Fin 2) ℝ) : ℂ :=
  2 * Real.pi * (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) /
    (((h 0 0 + h 1 1 : ℝ) : ℂ) + ((h 1 0 - h 0 1 : ℝ) : ℂ) * Complex.I))

theorem det_val (x : GL (Fin 2) ℝ) :
    ((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ) = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
  show (x : Matrix (Fin 2) (Fin 2) ℝ).det = _
  rw [Matrix.det_fin_two]

theorem S_I : S UpperHalfPlane.I = 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.I_im, UpperHalfPlane.I_re]

theorem eps_mul_eps : eps * eps = 1 := by
  apply Units.ext
  show (!![(1 : ℝ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, -1] = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_eps : ((Matrix.GeneralLinearGroup.det eps : ℝˣ) : ℝ) = -1 := by
  rw [det_val]; simp

theorem det_rot (θ : ℝ) : ((Matrix.GeneralLinearGroup.det (rot θ) : ℝˣ) : ℝ) = 1 := by
  rw [det_val]; simp; nlinarith [Real.cos_sq_add_sin_sq θ]

structure Good (F : GL (Fin 2) ℝ → ℂ) : Prop where
  cont : Continuous F
  rot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1), F (g * R a b hab) = (⟨a, b⟩ : ℂ) * F g
  cen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
    F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((t : ℝ) : ℂ) * F g
  hol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    ((z.im : ℝ) : ℂ)⁻¹ * F (m * S z)

theorem Good.left {F : GL (Fin 2) ℝ → ℂ} (hF : Good F) (g : GL (Fin 2) ℝ) :
    Good (fun x => F (g * x)) where
  cont := hF.cont.comp (continuous_const.mul continuous_id)
  rot := fun x a b hab => by simpa [mul_assoc] using hF.rot (g * x) a b hab
  cen := fun x t ht => by simpa [mul_assoc] using hF.cen (g * x) t ht
  hol := fun m => by simpa [mul_assoc] using hF.hol (g * m)

def fC (F : GL (Fin 2) ℝ → ℂ) : ℂ → ℂ :=
  (fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * F (S z)) ∘ UpperHalfPlane.ofComplex

theorem fC_coe (F : GL (Fin 2) ℝ → ℂ) (z : UpperHalfPlane) :
    fC F (z : ℂ) = ((z.im : ℝ) : ℂ)⁻¹ * F (S z) := by
  simp [fC, UpperHalfPlane.ofComplex_apply]

theorem fC_I (F : GL (Fin 2) ℝ → ℂ) : fC F Complex.I = F 1 := by
  rw [show (Complex.I : ℂ) = ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) from rfl, fC_coe, S_I]
  simp [UpperHalfPlane.I_im]

theorem differentiableOn_fC {F : GL (Fin 2) ℝ → ℂ} (hF : Good F) :
    DifferentiableOn ℂ (fC F) {z : ℂ | 0 < z.im} := by
  have h := hF.hol 1
  simp only [one_mul] at h
  exact UpperHalfPlane.mdifferentiable_iff.mp h

section Decomp

variable (x : GL (Fin 2) ℝ) (hx : 0 < ((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ))

def nsq : ℝ := (x 1 0 : ℝ) ^ 2 + (x 1 1 : ℝ) ^ 2

include hx in
theorem nsq_pos : 0 < nsq x := by
  unfold nsq
  by_contra h
  have h0 : (x 1 0 : ℝ) ^ 2 + (x 1 1 : ℝ) ^ 2 = 0 := le_antisymm (not_lt.mp h) (by positivity)
  have hc : (x 1 0 : ℝ) = 0 := by nlinarith [sq_nonneg (x 1 0 : ℝ), sq_nonneg (x 1 1 : ℝ)]
  have hd : (x 1 1 : ℝ) = 0 := by nlinarith [sq_nonneg (x 1 0 : ℝ), sq_nonneg (x 1 1 : ℝ)]
  rw [det_val, hc, hd] at hx; simp at hx

def lam : ℝ := Real.sqrt (nsq x)

include hx in
theorem lam_pos : 0 < lam x := Real.sqrt_pos.mpr (nsq_pos x hx)

include hx in
theorem lam_sq : lam x ^ 2 = nsq x := Real.sq_sqrt (nsq_pos x hx).le

include hx in
theorem rotpar : ((x 1 1 : ℝ) / lam x) ^ 2 + (-(x 1 0 : ℝ) / lam x) ^ 2 = 1 := by
  have hl := lam_pos x hx
  have hl2 := lam_sq x hx
  unfold nsq at hl2
  field_simp
  nlinarith [hl2]

def pt : UpperHalfPlane := x • UpperHalfPlane.I

include hx in
theorem coe_pt : ((pt x : UpperHalfPlane) : ℂ)
    = ((x 0 0 : ℝ) * Complex.I + (x 0 1 : ℝ)) / ((x 1 0 : ℝ) * Complex.I + (x 1 1 : ℝ)) := by
  unfold pt
  rw [UpperHalfPlane.coe_smul_of_det_pos hx]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem denomC_ne (C D : ℝ) (h : C ^ 2 + D ^ 2 ≠ 0) : (C : ℂ) * Complex.I + (D : ℂ) ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp at hre him
  apply h; rw [hre, him]; ring

include hx in
theorem pt_re : (pt x).re = ((x 0 1 : ℝ) * x 1 1 + (x 0 0 : ℝ) * x 1 0) / nsq x := by
  have hden := denomC_ne (x 1 0 : ℝ) (x 1 1 : ℝ) (nsq_pos x hx).ne'
  have h := coe_pt x hx
  rw [← UpperHalfPlane.coe_re, h]
  rw [Complex.div_re]
  simp [Complex.normSq_apply, nsq]
  have hns : ((x 1 0 : ℝ) * x 1 0 + (x 1 1 : ℝ) * x 1 1) ≠ 0 := by
    have := (nsq_pos x hx).ne'; unfold nsq at this; convert this using 1; ring
  field_simp
  ring

include hx in
theorem pt_im : (pt x).im = ((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ) / nsq x := by
  have hden := denomC_ne (x 1 0 : ℝ) (x 1 1 : ℝ) (nsq_pos x hx).ne'
  have h := coe_pt x hx
  rw [← UpperHalfPlane.coe_im, h, det_val]
  rw [Complex.div_im]
  simp [Complex.normSq_apply, nsq]
  have hns : ((x 1 0 : ℝ) * x 1 0 + (x 1 1 : ℝ) * x 1 1) ≠ 0 := by
    have := (nsq_pos x hx).ne'; unfold nsq at this; convert this using 1; ring
  field_simp
  ring

include hx in

theorem decomp :
    x = S (pt x) * R ((x 1 1 : ℝ) / lam x) (-(x 1 0 : ℝ) / lam x) (rotpar x hx) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (lam x) (lam_pos x hx).ne') := by
  have hl := lam_pos x hx
  have hl2 := lam_sq x hx
  have hns := (nsq_pos x hx).ne'
  have hre := pt_re x hx
  have him := pt_im x hx
  rw [det_val] at him
  apply Units.ext
  ext i j
  simp only [Units.val_mul]
  show (x : Matrix (Fin 2) (Fin 2) ℝ) i j
    = (!![((pt x).im : ℝ), ((pt x).re : ℝ); 0, 1] * !![(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x;
        -(-(x 1 0 : ℝ) / lam x), (x 1 1 : ℝ) / lam x] * (Matrix.scalar (Fin 2) (lam x))) i j
  rw [hre, him]
  unfold nsq at hl2 hns ⊢
  have hl0 : lam x ≠ 0 := hl.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal]
  · field_simp; nlinarith [hl2]
  · field_simp; nlinarith [hl2]
  · field_simp
  · field_simp

end Decomp

theorem af {F : GL (Fin 2) ℝ → ℂ} (hF : Good F) (x : GL (Fin 2) ℝ)
    (hx : 0 < ((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ)) :
    F x = (((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ) : ℂ) * fC F ((pt x : UpperHalfPlane) : ℂ) /
      (((x 1 0 : ℝ) : ℂ) * Complex.I + ((x 1 1 : ℝ) : ℂ)) := by
  have hl := lam_pos x hx
  have hl2 := lam_sq x hx
  have hns := (nsq_pos x hx).ne'
  have hden := denomC_ne (x 1 0 : ℝ) (x 1 1 : ℝ) hns
  have hdec := decomp x hx
  have hF1 : F x = ((lam x : ℝ) : ℂ) * ((⟨(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x⟩ : ℂ) *
      F (S (pt x))) := by
    conv_lhs => rw [hdec]
    rw [show S (pt x) * R ((x 1 1 : ℝ) / lam x) (-(x 1 0 : ℝ) / lam x) (rotpar x hx) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (lam x) (lam_pos x hx).ne')
        = 1 * (S (pt x) * R ((x 1 1 : ℝ) / lam x) (-(x 1 0 : ℝ) / lam x) (rotpar x hx)) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (lam x) (lam_pos x hx).ne') by group]
    rw [hF.cen _ _ hl, one_mul, hF.rot]
    rfl
  rw [hF1, fC_coe, pt_im x hx]
  have hy : (((pt x).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pt x).im_ne_zero
  have hδ : ((((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hnsC : ((nsq x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hns
  have hlC : ((lam x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'

  have key : ((lam x : ℝ) : ℂ) * (⟨(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x⟩ : ℂ)
      = (((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ) : ℂ) *
        (((((Matrix.GeneralLinearGroup.det x : ℝˣ) : ℝ) / nsq x : ℝ) : ℂ))⁻¹ /
        (((x 1 0 : ℝ) : ℂ) * Complex.I + ((x 1 1 : ℝ) : ℂ)) := by
    rw [eq_div_iff hden]
    have hmk : (⟨(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x⟩ : ℂ)
        = (((x 1 1 : ℝ) : ℂ) - ((x 1 0 : ℝ) : ℂ) * Complex.I) / ((lam x : ℝ) : ℂ) := by
      apply Complex.ext <;> simp <;> ring
    rw [hmk]
    push_cast
    field_simp
    have hl2C : ((lam x : ℝ) : ℂ) ^ 2 = ((nsq x : ℝ) : ℂ) := by exact_mod_cast hl2
    unfold nsq at hl2C ⊢
    push_cast at hl2C ⊢
    ring_nf
    rw [Complex.I_sq]
    ring
  calc ((lam x : ℝ) : ℂ) * ((⟨(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x⟩ : ℂ) * F (S (pt x)))
      = (((lam x : ℝ) : ℂ) * (⟨(x 1 1 : ℝ) / lam x, -(x 1 0 : ℝ) / lam x⟩ : ℂ)) * F (S (pt x)) := by
        ring
    _ = _ := by rw [key]; field_simp

section Mobius

variable (P : ℂ) (hP : 0 < P.im)

def Yf (ζ : ℂ) : ℂ := (1 - Complex.I * P) + ζ * (1 + Complex.I * P)

def Nf (ζ : ℂ) : ℂ := (ζ + 1) * P + (1 - ζ) * Complex.I

def Mob (ζ : ℂ) : ℂ := Nf P ζ / Yf P ζ

theorem norm_sq_onePlus : ‖1 + Complex.I * P‖ ^ 2 = (1 - P.im) ^ 2 + P.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

theorem norm_sq_oneMinus : ‖1 - Complex.I * P‖ ^ 2 = (1 + P.im) ^ 2 + P.re ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

include hP in
theorem norm_lt : ‖1 + Complex.I * P‖ < ‖1 - Complex.I * P‖ := by
  have h1 := norm_sq_onePlus P
  have h2 := norm_sq_oneMinus P
  nlinarith [norm_nonneg (1 + Complex.I * P), norm_nonneg (1 - Complex.I * P)]

include hP in
theorem oneMinus_ne : 1 - Complex.I * P ≠ 0 := by
  intro h
  have := norm_lt P hP
  rw [h, norm_zero] at this
  exact (not_lt.mpr (norm_nonneg _)) this

def rad : ℝ := (‖1 - Complex.I * P‖ + 1) / (‖1 + Complex.I * P‖ + 1)

include hP in
theorem one_lt_rad : 1 < rad P := by
  unfold rad
  rw [lt_div_iff₀ (by positivity)]
  linarith [norm_lt P hP]

include hP in
theorem key_lt {ζ : ℂ} (hζ : ‖ζ‖ < rad P) : ‖1 + Complex.I * P‖ * ‖ζ‖ < ‖1 - Complex.I * P‖ := by
  have hlt := norm_lt P hP
  unfold rad at hζ
  have ha := norm_nonneg (1 + Complex.I * P)
  have hz := norm_nonneg ζ
  by_cases h0 : ‖1 + Complex.I * P‖ = 0
  · rw [h0, zero_mul]; linarith
  · have hpos : 0 < ‖1 + Complex.I * P‖ := lt_of_le_of_ne ha (Ne.symm h0)
    calc ‖1 + Complex.I * P‖ * ‖ζ‖
        < ‖1 + Complex.I * P‖ * ((‖1 - Complex.I * P‖ + 1) / (‖1 + Complex.I * P‖ + 1)) :=
          mul_lt_mul_of_pos_left hζ hpos
      _ ≤ ‖1 - Complex.I * P‖ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith

include hP in
theorem Yf_ne {ζ : ℂ} (hζ : ‖ζ‖ < rad P) : Yf P ζ ≠ 0 := by
  intro h
  have hk := key_lt P hP hζ
  have : 1 - Complex.I * P = -(ζ * (1 + Complex.I * P)) := by
    unfold Yf at h; linear_combination h
  have hn : ‖1 - Complex.I * P‖ = ‖ζ‖ * ‖1 + Complex.I * P‖ := by
    rw [this, norm_neg, norm_mul]
  rw [hn] at hk
  linarith

theorem im_formula (ζ : ℂ) :
    (Nf P ζ * (starRingEnd ℂ) (Yf P ζ)).im
      = ((1 + P.im) ^ 2 + P.re ^ 2) - ((1 - P.im) ^ 2 + P.re ^ 2) * (ζ.re ^ 2 + ζ.im ^ 2) := by
  simp [Nf, Yf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

include hP in
theorem Mob_im_pos {ζ : ℂ} (hζ : ‖ζ‖ < rad P) : 0 < (Mob P ζ).im := by
  have hY := Yf_ne P hP hζ
  have hk := key_lt P hP hζ
  unfold Mob
  rw [Complex.div_im]
  have hns : 0 < Complex.normSq (Yf P ζ) := Complex.normSq_pos.mpr hY
  rw [div_sub_div_same]
  apply div_pos _ hns
  have h := im_formula P ζ
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
  have h' : (Nf P ζ).im * (Yf P ζ).re - (Nf P ζ).re * (Yf P ζ).im
      = ((1 + P.im) ^ 2 + P.re ^ 2) - ((1 - P.im) ^ 2 + P.re ^ 2) * (ζ.re ^ 2 + ζ.im ^ 2) := by
    linarith
  rw [h']
  have hζ2 : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hζ2, ← norm_sq_onePlus, ← norm_sq_oneMinus, ← mul_pow]
  have ha := norm_nonneg (1 + Complex.I * P)
  have hz := norm_nonneg ζ
  nlinarith [mul_nonneg ha hz]

include hP in
theorem Mob_zero : Mob P 0 = Complex.I := by
  unfold Mob Nf Yf
  rw [div_eq_iff (by simpa using oneMinus_ne P hP)]
  ring_nf; rw [Complex.I_sq]; ring

theorem differentiableOn_Yf : Differentiable ℂ (Yf P) := by
  unfold Yf; fun_prop

theorem differentiableOn_Nf : Differentiable ℂ (Nf P) := by
  unfold Nf; fun_prop

include hP in
theorem differentiableOn_Mob : DifferentiableOn ℂ (Mob P) (ball 0 (rad P)) := by
  intro ζ hζ
  have hζ' : ‖ζ‖ < rad P := by simpa using hζ
  exact (((differentiableOn_Nf P).differentiableAt).div ((differentiableOn_Yf P).differentiableAt)
    (Yf_ne P hP hζ')).differentiableWithinAt

theorem cos_uform (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) = (cexp (θ * Complex.I) + (cexp (θ * Complex.I))⁻¹) / 2 := by
  rw [Complex.ofReal_cos, ← Complex.exp_neg, eq_div_iff two_ne_zero, mul_comm, Complex.two_cos, neg_mul]

theorem sin_uform (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ) = ((cexp (θ * Complex.I))⁻¹ - cexp (θ * Complex.I)) * Complex.I / 2 := by
  rw [Complex.ofReal_sin, ← Complex.exp_neg, eq_div_iff two_ne_zero, mul_comm, Complex.two_sin, neg_mul]

theorem denom_uform (u : ℂ) (hu : u ≠ 0) :
    (u + u⁻¹) / 2 - ((u⁻¹ - u) * Complex.I / 2) * P = u⁻¹ * Yf P (u ^ 2) / 2 := by
  unfold Yf; field_simp; ring

theorem num_uform (u : ℂ) (hu : u ≠ 0) :
    (u + u⁻¹) / 2 * P + (u⁻¹ - u) * Complex.I / 2 = u⁻¹ * Nf P (u ^ 2) / 2 := by
  unfold Nf; field_simp

end Mobius

theorem norm_exp_mul_I_sq (θ : ℝ) : ‖cexp (θ * Complex.I) ^ 2‖ = 1 := by
  rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem exp_sq_eq_circleMap (θ : ℝ) : cexp (θ * Complex.I) ^ 2 = circleMap 0 1 (2 * θ) := by
  rw [circleMap, ← Complex.exp_nat_mul]; push_cast; ring_nf

theorem integral_doubled {H : ℂ → ℂ} {r : ℝ} (hr : 1 < r) (hH : DifferentiableOn ℂ H (ball 0 r)) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, H (cexp (θ * Complex.I) ^ 2) = 2 * Real.pi * H 0 := by
  set f : ℝ → ℂ := fun θ => H (circleMap 0 1 θ) with hf
  have hcont : Continuous f := by
    refine hH.continuousOn.comp_continuous (continuous_circleMap 0 1) fun θ => ?_
    simp only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_one]
    exact hr
  have hper : Function.Periodic f (2 * Real.pi) := fun θ => by
    simp only [hf]; rw [periodic_circleMap]
  have h1 : (∫ θ in (0 : ℝ)..2 * Real.pi, H (cexp (θ * Complex.I) ^ 2))
      = ∫ θ in (0 : ℝ)..2 * Real.pi, f (2 * θ) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hf, exp_sq_eq_circleMap]
  rw [h1, intervalIntegral.integral_comp_mul_left f two_ne_zero]
  simp only [mul_zero]
  have h4π : (2 : ℝ) * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi := by ring
  rw [h4π, ← intervalIntegral.integral_add_adjacent_intervals (b := 2 * Real.pi)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hshift : (∫ θ in (2 * Real.pi)..(2 * Real.pi + 2 * Real.pi), f θ)
      = ∫ θ in (0 : ℝ)..(0 + 2 * Real.pi), f θ := hper.intervalIntegral_add_eq _ _
  rw [hshift, zero_add]
  have havg : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = (2 * Real.pi : ℝ) • Real.circleAverage H 0 1 := by
    rw [Real.circleAverage_def, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hmv : Real.circleAverage H 0 1 = H 0 := by
    refine DiffContOnCl.circleAverage ?_
    refine DifferentiableOn.diffContOnCl ?_
    rw [abs_one, closure_ball (0 : ℂ) one_ne_zero]
    exact hH.mono (closedBall_subset_ball hr)
  rw [havg, hmv]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem integral_doubled_mul {H : ℂ → ℂ} {r : ℝ} (hr : 1 < r) (hH : DifferentiableOn ℂ H (ball 0 r)) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, cexp (θ * Complex.I) ^ 2 * H (cexp (θ * Complex.I) ^ 2) = 0 := by
  have h := integral_doubled (H := fun η => η * H η) hr ((differentiableOn_id).mul hH)
  simpa using h

section Core

variable {F : GL (Fin 2) ℝ → ℂ} (hF : Good F) (h : GL (Fin 2) ℝ)
  (hh : 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ))

def Pt : ℂ := ((pt h : UpperHalfPlane) : ℂ)

theorem Pt_im_pos : 0 < (Pt h).im := (pt h).im_pos

def Hh : ℂ → ℂ := fun ζ =>
  (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) / (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ)))
    * fC F (Mob (Pt h) ζ) / Yf (Pt h) ζ

include hF hh in
theorem differentiableOn_Hh : DifferentiableOn ℂ (Hh h (F := F)) (ball 0 (rad (Pt h))) := by
  have hP := Pt_im_pos h
  unfold Hh
  refine DifferentiableOn.div (DifferentiableOn.const_mul ?_ _) (differentiableOn_Yf _).differentiableOn
    (fun ζ hζ => Yf_ne _ hP (by simpa using hζ))
  refine (differentiableOn_fC hF).comp (differentiableOn_Mob _ hP) fun ζ hζ => ?_
  exact Mob_im_pos _ hP (by simpa using hζ)

include hh in
theorem Hh_zero : Hh h (F := F) 0
    = 2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) * F 1 /
      ((((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ)) * (1 - Complex.I * Pt h)) := by
  have hP := Pt_im_pos h
  unfold Hh
  rw [Mob_zero _ hP, fC_I]
  unfold Yf
  simp only [zero_mul, add_zero]
  have hden := denomC_ne (h 1 0 : ℝ) (h 1 1 : ℝ) (nsq_pos h hh).ne'
  have h1 := oneMinus_ne _ hP
  field_simp

include hh in

theorem rot_mul_apply (θ : ℝ) (i j : Fin 2) :
    ((rot θ * h : GL (Fin 2) ℝ) i j : ℝ)
      = (rot θ) i 0 * h 0 j + (rot θ) i 1 * h 1 j := by
  show ((rot θ : Matrix (Fin 2) (Fin 2) ℝ) * (h : Matrix (Fin 2) (Fin 2) ℝ)) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem rot_apply (θ : ℝ) :
    ((rot θ) 0 0 : ℝ) = Real.cos θ ∧ ((rot θ) 0 1 : ℝ) = Real.sin θ ∧
      ((rot θ) 1 0 : ℝ) = -Real.sin θ ∧ ((rot θ) 1 1 : ℝ) = Real.cos θ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

include hh in
theorem det_rot_mul (θ : ℝ) :
    ((Matrix.GeneralLinearGroup.det (rot θ * h) : ℝˣ) : ℝ)
      = ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) := by
  rw [map_mul, Units.val_mul, det_rot, one_mul]

include hh in

theorem coe_pt_rot_mul (θ : ℝ) :
    ((pt (rot θ * h) : UpperHalfPlane) : ℂ)
      = (((Real.cos θ : ℝ) : ℂ) * Pt h + ((Real.sin θ : ℝ) : ℂ)) /
        (-((Real.sin θ : ℝ) : ℂ) * Pt h + ((Real.cos θ : ℝ) : ℂ)) := by
  unfold pt Pt
  rw [mul_smul]
  unfold pt
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_rot]; exact one_pos)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

include hh in
theorem Pt_mul_denom :
    Pt h * (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ))
      = ((h 0 0 : ℝ) : ℂ) * Complex.I + ((h 0 1 : ℝ) : ℂ) := by
  have hden := denomC_ne (h 1 0 : ℝ) (h 1 1 : ℝ) (nsq_pos h hh).ne'
  unfold Pt
  rw [coe_pt h hh, div_mul_cancel₀ _ hden]

include hF hh in

theorem pointwise (θ : ℝ) :
    cexp (-(θ * Complex.I)) * F (rot θ * h) = Hh h (F := F) (cexp (θ * Complex.I) ^ 2) := by
  have hP := Pt_im_pos h
  set u : ℂ := cexp (θ * Complex.I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hunorm : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hu2 : ‖u ^ 2‖ < rad (Pt h) := by
    rw [norm_pow, hunorm, one_pow]; exact one_lt_rad _ hP
  have hden := denomC_ne (h 1 0 : ℝ) (h 1 1 : ℝ) (nsq_pos h hh).ne'
  have hδ : 0 < ((Matrix.GeneralLinearGroup.det (rot θ * h) : ℝˣ) : ℝ) := by
    rw [det_rot_mul h hh]; exact hh

  rw [af hF (rot θ * h) hδ, det_rot_mul h hh, coe_pt_rot_mul h hh]

  have hrow : (((rot θ * h : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * Complex.I + (((rot θ * h : GL (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
      = (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ)) *
        (((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Pt h) := by
    rw [rot_mul_apply h hh θ 1 0, rot_mul_apply h hh θ 1 1]
    obtain ⟨_, _, h10, h11⟩ := rot_apply θ
    rw [h10, h11]
    have hP' := Pt_mul_denom h hh
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination ((Real.sin θ : ℝ) : ℂ) * hP'
  rw [hrow]

  have hcos := cos_uform θ
  have hsin := sin_uform θ
  rw [← hu] at hcos hsin
  have hY := Yf_ne _ hP hu2
  have hd1 : ((Real.cos θ : ℝ) : ℂ) - ((Real.sin θ : ℝ) : ℂ) * Pt h = u⁻¹ * Yf (Pt h) (u ^ 2) / 2 := by
    rw [hcos, hsin]; exact denom_uform _ u hu0
  have hd2 : -((Real.sin θ : ℝ) : ℂ) * Pt h + ((Real.cos θ : ℝ) : ℂ) = u⁻¹ * Yf (Pt h) (u ^ 2) / 2 := by
    rw [← hd1]; ring
  have hn2 : ((Real.cos θ : ℝ) : ℂ) * Pt h + ((Real.sin θ : ℝ) : ℂ) = u⁻¹ * Nf (Pt h) (u ^ 2) / 2 := by
    rw [hcos, hsin]; exact num_uform _ u hu0
  rw [hd1, hd2, hn2]
  have hmob : u⁻¹ * Nf (Pt h) (u ^ 2) / 2 / (u⁻¹ * Yf (Pt h) (u ^ 2) / 2) = Mob (Pt h) (u ^ 2) := by
    unfold Mob
    field_simp
  rw [hmob]
  have hexp : cexp (-(θ * Complex.I)) = u⁻¹ := by rw [hu, Complex.exp_neg]
  rw [hexp]
  unfold Hh
  field_simp

include hF hh in

theorem integral_pos :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cexp (-(θ * Complex.I)) * F (rot θ * h)) = coeffC h * F 1 := by
  have hP := Pt_im_pos h
  simp_rw [pointwise hF h hh]
  rw [integral_doubled (one_lt_rad _ hP) (differentiableOn_Hh hF h hh), Hh_zero h hh]
  unfold coeffC
  have hden := denomC_ne (h 1 0 : ℝ) (h 1 1 : ℝ) (nsq_pos h hh).ne'
  have h1 := oneMinus_ne _ hP
  have hiii : (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ)) * (1 - Complex.I * Pt h)
      = (((h 0 0 + h 1 1 : ℝ)) : ℂ) + (((h 1 0 - h 0 1 : ℝ)) : ℂ) * Complex.I := by
    have hP' := Pt_mul_denom h hh
    rw [mul_sub, mul_one, show (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ)) * (Complex.I * Pt h)
      = Complex.I * (Pt h * (((h 1 0 : ℝ) : ℂ) * Complex.I + ((h 1 1 : ℝ) : ℂ))) by ring, hP']
    push_cast
    ring_nf; rw [Complex.I_sq]; ring
  rw [hiii]
  have hne : (((h 0 0 + h 1 1 : ℝ)) : ℂ) + (((h 1 0 - h 0 1 : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    rw [← hiii]; exact mul_ne_zero hden h1
  field_simp

include hF hh in

theorem integral_neg_weight :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cexp (θ * Complex.I) * F (rot θ * h)) = 0 := by
  have hP := Pt_im_pos h
  have hpt : ∀ θ : ℝ, cexp (θ * Complex.I) * F (rot θ * h)
      = cexp (θ * Complex.I) ^ 2 * Hh h (F := F) (cexp (θ * Complex.I) ^ 2) := by
    intro θ
    rw [← pointwise hF h hh θ, sq, mul_assoc, ← mul_assoc (cexp (θ * Complex.I)) (cexp (-(θ * _))),
      ← Complex.exp_add]
    simp
  simp_rw [hpt]
  exact integral_doubled_mul (one_lt_rad _ hP) (differentiableOn_Hh hF h hh)

end Core

theorem differentiableAt_conj_negConj {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (-(starRingEnd ℂ) z)) :
    DifferentiableAt ℂ (fun w => (starRingEnd ℂ) (f (-(starRingEnd ℂ) w))) z := by
  set φ : ℂ → ℂ := fun w => -(starRingEnd ℂ) w with hφ
  have hφc : Continuous φ := (Complex.continuous_conj.comp continuous_id).neg
  have hd : HasDerivAt f (deriv f (φ z)) (φ z) := hf.hasDerivAt
  have h1 := (hasDerivAt_iff_isLittleO.mp hd).comp_tendsto (hφc.tendsto z)
  have h2 : HasDerivAt (fun w => (starRingEnd ℂ) (f (φ w))) (-(starRingEnd ℂ) (deriv f (φ z))) z := by
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsLittleO.of_norm_norm ?_
    have h1n := h1.norm_norm
    have hl : (fun x => ‖((fun x' => f x' - f (φ z) - (x' - φ z) • deriv f (φ z)) ∘ φ) x‖)
        = fun w => ‖(starRingEnd ℂ) (f (φ w)) - (starRingEnd ℂ) (f (φ z))
            - (w - z) • -(starRingEnd ℂ) (deriv f (φ z))‖ := by
      funext w
      rw [← Complex.norm_conj]
      congr 1
      simp only [Function.comp_apply, smul_eq_mul, map_sub, map_mul, hφ, map_neg, Complex.conj_conj]
      ring
    have hr : (fun w => ‖((fun x' => x' - φ z) ∘ φ) w‖) = fun w => ‖w - z‖ := by
      funext w
      simp only [Function.comp_apply, hφ]
      rw [show -(starRingEnd ℂ) w - -(starRingEnd ℂ) z = (starRingEnd ℂ) (z - w) by
        rw [map_sub]; ring, Complex.norm_conj, norm_sub_rev]
    rw [hl, hr] at h1n
    exact h1n
  exact h2.differentiableAt

def negConj (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-(starRingEnd ℂ) (z : ℂ), by simpa using z.im_pos⟩

theorem negConj_im (z : UpperHalfPlane) : (negConj z).im = z.im := by
  show (-(starRingEnd ℂ) (z : ℂ)).im = z.im
  simp

theorem negConj_re (z : UpperHalfPlane) : (negConj z).re = -z.re := by
  show (-(starRingEnd ℂ) (z : ℂ)).re = -z.re
  simp

theorem S_mul_eps (z : UpperHalfPlane) : S z * eps = eps * S (negConj z) := by
  apply Units.ext
  show (!![(z.im : ℝ), (z.re : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, -1]
    = !![(1 : ℝ), 0; 0, -1] * !![((negConj z).im : ℝ), ((negConj z).re : ℝ); 0, 1]
  rw [negConj_im, negConj_re]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem R_mul_eps (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    R a b hab * eps = eps * R a (-b) (by simpa using hab) := by
  apply Units.ext
  show (!![a, b; -b, a] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, -1]
    = !![(1 : ℝ), 0; 0, -1] * !![a, -b; -(-b), a]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_mul_eps (t : ℝˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) t * eps = eps * Matrix.GeneralLinearGroup.scalar (Fin 2) t := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (t : ℝ) * (!![(1 : ℝ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)
    = !![(1 : ℝ), 0; 0, -1] * Matrix.scalar (Fin 2) (t : ℝ)
  exact (Matrix.scalar_commute (t : ℝ) (fun r => mul_comm _ r) _).eq

theorem Good.conjEps {F : GL (Fin 2) ℝ → ℂ} (hF : Good F) :
    Good (fun x => (starRingEnd ℂ) (F (x * eps))) where
  cont := Complex.continuous_conj.comp (hF.cont.comp (continuous_id.mul continuous_const))
  rot := fun g a b hab => by
    show (starRingEnd ℂ) (F (g * R a b hab * eps)) = _
    rw [mul_assoc, R_mul_eps, ← mul_assoc, hF.rot, map_mul]
    congr 1
    apply Complex.ext <;> simp
  cen := fun g t ht => by
    show (starRingEnd ℂ) (F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t * eps)) = _
    rw [mul_assoc, scalar_mul_eps, ← mul_assoc, hF.cen _ _ ht, map_mul, Complex.conj_ofReal]
  hol := fun m => by
    have h := hF.hol (m * eps)
    rw [UpperHalfPlane.mdifferentiable_iff] at h ⊢
    have heq : ∀ w ∈ {z : ℂ | 0 < z.im},
        ((fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (F (m * S z * eps))) ∘
          UpperHalfPlane.ofComplex) w
        = (starRingEnd ℂ) (((fun z : UpperHalfPlane => ((z.im : ℝ) : ℂ)⁻¹ * F (m * eps * S z)) ∘
          UpperHalfPlane.ofComplex) (-(starRingEnd ℂ) w)) := by
      intro w hw
      have hw' : 0 < (-(starRingEnd ℂ) w).im := by simpa using hw
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      rw [mul_assoc, S_mul_eps, ← mul_assoc]
      have hpt : negConj ⟨w, hw⟩ = ⟨-(starRingEnd ℂ) w, hw'⟩ := rfl
      rw [hpt, map_mul]
      congr 1
      simp
    refine DifferentiableOn.congr (fun w hw => ?_) heq
    have hw' : 0 < (-(starRingEnd ℂ) w).im := by simpa using hw
    exact (differentiableAt_conj_negConj (h.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw'))).differentiableWithinAt

end Q1WtOneProj

end

open Q1WtOneProj in
theorem solution
    (F : GL (Fin 2) ℝ → ℂ) (hF : Continuous F)
    (hrot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * F g)
    (hcen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
      F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((t : ℝ) : ℂ) * F g)
    (hhol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * F (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)))
    (h g : GL (Fin 2) ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(θ * Complex.I)) *
        F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
          (by rw [Matrix.det_fin_two_of, show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ
                = Real.cos θ ^ 2 + Real.sin θ ^ 2 by ring, Real.cos_sq_add_sin_sq]
              exact one_ne_zero) * h)) =
      (if 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) then
          2 * Real.pi * (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) /
            (((h 0 0 + h 1 1 : ℝ) : ℂ) + ((h 1 0 - h 0 1 : ℝ) : ℂ) * Complex.I))
        else 0) * F g := by
  have hG : Good F := ⟨hF, fun g a b hab => hrot g a b hab, hcen, hhol⟩
  by_cases hdet : 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ)
  · rw [if_pos hdet]
    have hI := integral_pos (hG.left g) h hdet
    simp only [mul_one] at hI
    have hI' : (∫ θ in (0 : ℝ)..2 * Real.pi, cexp (-(θ * Complex.I)) * F (g * rot θ * h))
        = coeffC h * F g := by
      simpa [mul_assoc] using hI
    rw [hI']
    unfold coeffC
    ring
  · rw [if_neg hdet, zero_mul]
    have hne : ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
    have hlt : ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hdet) hne
    set hp : GL (Fin 2) ℝ := h * eps with hhp
    have hpos : 0 < ((Matrix.GeneralLinearGroup.det hp : ℝˣ) : ℝ) := by
      rw [hhp, map_mul, Units.val_mul, det_eps]; linarith
    have hG3 := (hG.conjEps).left g
    have hzero := integral_neg_weight hG3 hp hpos

    have hint : ∀ θ : ℝ, cexp (-(θ * Complex.I)) * F (g * rot θ * h)
        = (starRingEnd ℂ) (cexp (θ * Complex.I) * (starRingEnd ℂ) (F (g * (rot θ * hp) * eps))) := by
      intro θ
      rw [map_mul, Complex.conj_conj, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 2
      · ring
      · rw [hhp]; simp only [mul_assoc, eps_mul_eps, mul_one]
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc (∫ θ in (0 : ℝ)..2 * Real.pi, cexp (-(θ * Complex.I)) * F (g * rot θ * h))
        = ∫ θ in (0 : ℝ)..2 * Real.pi, (starRingEnd ℂ)
            (cexp (θ * Complex.I) * (starRingEnd ℂ) (F (g * (rot θ * hp) * eps))) :=
          intervalIntegral.integral_congr fun θ _ => hint θ
      _ = (starRingEnd ℂ) (∫ θ in (0 : ℝ)..2 * Real.pi,
            cexp (θ * Complex.I) * (starRingEnd ℂ) (F (g * (rot θ * hp) * eps))) := by
          rw [intervalIntegral.integral_of_le h2π, intervalIntegral.integral_of_le h2π, integral_conj]
      _ = 0 := by rw [hzero, map_zero]

end S_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq
end P2MW
export P2MW.S_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq (solution)
