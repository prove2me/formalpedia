-- Prove2me | solution 1 for AutomorphicForm.RealIwasawa.norm_fourierIntegral_cpow_rad_mul_le_polyDecay
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a24dc32d-b13b-51ef-ad16-5e2a6a9abb39

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open scoped ContDiff Nat

namespace M4aP3B
namespace RealIwasawa

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

@[scoped simp] theorem rot_apply_00 (θ : ℝ) : rot θ 0 0 = Real.cos θ := rfl
@[scoped simp] theorem rot_apply_01 (θ : ℝ) : rot θ 0 1 = -Real.sin θ := rfl
@[scoped simp] theorem rot_apply_10 (θ : ℝ) : rot θ 1 0 = Real.sin θ := rfl
@[scoped simp] theorem rot_apply_11 (θ : ℝ) : rot θ 1 1 = Real.cos θ := rfl

theorem rot_zero : rot 0 = 1 := by
  rw [rot, Matrix.one_fin_two, Real.cos_zero, Real.sin_zero, neg_zero]

theorem rot_add (s t : ℝ) : rot (s + t) = rot s * rot t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  rw [rot, Matrix.det_fin_two_of]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination h

theorem rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  rw [← rot_add, add_neg_cancel, rot_zero]

theorem rot_neg_mul_rot (θ : ℝ) : rot (-θ) * rot θ = 1 := by
  rw [← rot_add, neg_add_cancel, rot_zero]

theorem row_sq_rot (θ x y : ℝ) :
    (x * rot θ 0 0 + y * rot θ 1 0) ^ 2 + (x * rot θ 0 1 + y * rot θ 1 1) ^ 2 = x ^ 2 + y ^ 2 := by
  simp only [rot_apply_00, rot_apply_01, rot_apply_10, rot_apply_11]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination (x ^ 2 + y ^ 2) * h

theorem norm_det_rot (θ : ℝ) : ‖(rot θ).det‖ = 1 := by
  rw [det_rot, norm_one]

theorem norm_row_sq_rot (θ x y : ℝ) :
    ‖x * rot θ 0 0 + y * rot θ 1 0‖ ^ 2 + ‖x * rot θ 0 1 + y * rot θ 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Real.norm_eq_abs, sq_abs]
  exact row_sq_rot θ x y

theorem continuous_rot : Continuous rot := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · show Continuous fun θ => Real.cos θ
    exact Real.continuous_cos
  · show Continuous fun θ => -Real.sin θ
    exact Real.continuous_sin.neg
  · show Continuous fun θ => Real.sin θ
    exact Real.continuous_sin
  · show Continuous fun θ => Real.cos θ
    exact Real.continuous_cos

theorem contDiff_rot_apply (i j : Fin 2) : ContDiff ℝ ∞ (fun θ => rot θ i j) := by
  fin_cases i <;> fin_cases j
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos
  · show ContDiff ℝ ∞ fun θ => -Real.sin θ
    exact Real.contDiff_sin.neg
  · show ContDiff ℝ ∞ fun θ => Real.sin θ
    exact Real.contDiff_sin
  · show ContDiff ℝ ∞ fun θ => Real.cos θ
    exact Real.contDiff_cos

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  ⟨rot θ, rot (-θ), rot_mul_rot_neg θ, rot_neg_mul_rot θ⟩

@[scoped simp] theorem coe_rotGL (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rot θ := rfl

theorem rotGL_zero : rotGL 0 = 1 := Units.ext rot_zero

theorem rotGL_add (s t : ℝ) : rotGL (s + t) = rotGL s * rotGL t := Units.ext (rot_add s t)

theorem continuous_rotGL : Continuous rotGL := by
  refine Units.continuous_iff.2 ⟨continuous_rot, ?_⟩
  show Continuous fun θ => rot (-θ)
  exact continuous_rot.comp continuous_neg

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

def weylUnip (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0] * !![1, u; 0, 1] * g

theorem weylUnip_eq (u : ℝ) :
    weylUnip g u = !![g 1 0, g 1 1; g 0 0 + u * g 1 0, g 0 1 + u * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylUnip, Matrix.mul_apply, Fin.sum_univ_two]

def botNormSq : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

def foot : ℝ := -(g 0 0 * g 1 0 + g 0 1 * g 1 1) / botNormSq g

def center : ℂ := ⟨foot g, -(g.det / botNormSq g)⟩

def dir : ℂ := ⟨g 1 1, g 1 0⟩

def botRow (u : ℝ) : ℂ := ⟨g 0 1 + u * g 1 1, g 0 0 + u * g 1 0⟩

def rad (u : ℝ) : ℝ := ‖botRow g u‖

variable {g}

theorem botNormSq_pos (hg : g.det ≠ 0) : 0 < botNormSq g := by
  unfold botNormSq
  rcases (add_nonneg (sq_nonneg (g 1 0)) (sq_nonneg (g 1 1))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hd : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero]

theorem norm_dir_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : ‖dir g‖ ^ 2 = botNormSq g := by
  rw [Complex.sq_norm, dir, Complex.normSq_mk, botNormSq]
  ring

theorem norm_dir_pos (hg : g.det ≠ 0) : 0 < ‖dir g‖ := by
  have h := norm_dir_sq g
  have hA := botNormSq_pos hg
  nlinarith [norm_nonneg (dir g)]

theorem dir_ne_zero (hg : g.det ≠ 0) : dir g ≠ 0 :=
  norm_pos_iff.1 (norm_dir_pos hg)

theorem botRow_eq (hg : g.det ≠ 0) (u : ℝ) : botRow g u = dir g * ((u : ℂ) - center g) := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  apply Complex.ext
  · simp only [botRow, dir, center, foot, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring
  · simp only [botRow, dir, center, foot, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, Matrix.det_fin_two]
    unfold botNormSq at hA ⊢
    field_simp
    ring

theorem im_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    ((u : ℂ) - center g).im = g.det / botNormSq g := by
  simp [center]

theorem re_sub_center (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : ((u : ℂ) - center g).re = u - foot g := by
  simp [center]

theorem sub_center_mem_slitPlane (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr (by
    rw [im_sub_center]
    exact div_ne_zero hg (botNormSq_pos hg).ne'))

theorem sub_center_ne_zero (hg : g.det ≠ 0) (u : ℝ) : (u : ℂ) - center g ≠ 0 :=
  Complex.slitPlane_ne_zero (sub_center_mem_slitPlane hg u)

theorem abs_det_div_le_norm_sub_center (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / botNormSq g ≤ ‖(u : ℂ) - center g‖ := by
  have h := Complex.abs_im_le_norm ((u : ℂ) - center g)
  rwa [im_sub_center, abs_div, abs_of_pos (botNormSq_pos hg)] at h

theorem rad_eq (hg : g.det ≠ 0) (u : ℝ) : rad g u = ‖dir g‖ * ‖(u : ℂ) - center g‖ := by
  rw [rad, botRow_eq hg, norm_mul]

theorem rad_pos (hg : g.det ≠ 0) (u : ℝ) : 0 < rad g u := by
  rw [rad_eq hg]
  exact mul_pos (norm_dir_pos hg) (norm_pos_iff.2 (sub_center_ne_zero hg u))

theorem rad_sq (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u ^ 2 = (g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2 := by
  rw [rad, Complex.sq_norm, botRow, Complex.normSq_mk]
  ring

theorem rad_eq_sqrt (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    rad g u = Real.sqrt ((g 0 0 + u * g 1 0) ^ 2 + (g 0 1 + u * g 1 1) ^ 2) := by
  rw [← rad_sq, Real.sqrt_sq (show 0 ≤ rad g u from norm_nonneg _)]

theorem rad_sq_eq (hg : g.det ≠ 0) (u : ℝ) :
    rad g u ^ 2 = botNormSq g * (u - foot g) ^ 2 + g.det ^ 2 / botNormSq g := by
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  rw [rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm, ← Complex.re_add_im ((u : ℂ) - center g),
    re_sub_center, im_sub_center]
  rw [Complex.normSq_add_mul_I]
  field_simp

theorem abs_det_div_sqrt_le_rad (hg : g.det ≠ 0) (u : ℝ) :
    |g.det| / Real.sqrt (botNormSq g) ≤ rad g u := by
  have hA := botNormSq_pos hg
  have hdir : ‖dir g‖ = Real.sqrt (botNormSq g) := by
    rw [← norm_dir_sq, Real.sqrt_sq (norm_nonneg _)]
  have hs : 0 < Real.sqrt (botNormSq g) := Real.sqrt_pos.2 hA
  have h1 : |g.det| ≤ ‖(u : ℂ) - center g‖ * botNormSq g :=
    (div_le_iff₀ hA).1 (abs_det_div_le_norm_sub_center hg u)
  rw [rad_eq hg, hdir, div_le_iff₀ hs]
  calc |g.det| ≤ ‖(u : ℂ) - center g‖ * botNormSq g := h1
    _ = Real.sqrt (botNormSq g) * ‖(u : ℂ) - center g‖ * Real.sqrt (botNormSq g) := by
        rw [mul_comm (Real.sqrt (botNormSq g)) _, mul_assoc, Real.mul_self_sqrt hA.le]

variable (g)

def logLine (u : ℝ) : ℂ := Complex.log ((u : ℂ) - center g)

def angle (u : ℝ) : ℝ := Complex.arg (dir g) + (logLine g u).im

variable {g}

theorem angle_eq_arg_add_arg (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    angle g u = Complex.arg (dir g) + Complex.arg ((u : ℂ) - center g) := by
  rw [angle, logLine, Complex.log_im]

theorem log_rad_eq (hg : g.det ≠ 0) (u : ℝ) : Real.log (rad g u) = Real.log ‖dir g‖ + (logLine g u).re := by
  rw [rad_eq hg, Real.log_mul (norm_dir_pos hg).ne' (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne', logLine,
    Complex.log_re]

theorem exp_angle_mul_I (hg : g.det ≠ 0) (u : ℝ) :
    Complex.exp (angle g u * Complex.I) = botRow g u / rad g u := by
  have h1 : Complex.exp (Complex.arg (dir g) * Complex.I) = dir g / ‖dir g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_dir_pos hg).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I (dir g))
  have h2 : Complex.exp (Complex.arg ((u : ℂ) - center g) * Complex.I)
      = ((u : ℂ) - center g) / ‖(u : ℂ) - center g‖ := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.2 (norm_pos_iff.2 (sub_center_ne_zero hg u)).ne')]
    exact (mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I _)
  rw [angle_eq_arg_add_arg, Complex.ofReal_add, add_mul, Complex.exp_add, h1, h2, div_mul_div_comm,
    ← botRow_eq hg, rad_eq hg, Complex.ofReal_mul]

theorem cos_angle (hg : g.det ≠ 0) (u : ℝ) : Real.cos (angle g u) = (g 0 1 + u * g 1 1) / rad g u := by
  have h := congrArg Complex.re (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_re, Complex.div_ofReal_re] at h
  rw [h, botRow]

theorem sin_angle (hg : g.det ≠ 0) (u : ℝ) : Real.sin (angle g u) = (g 0 0 + u * g 1 0) / rad g u := by
  have h := congrArg Complex.im (exp_angle_mul_I hg u)
  rw [Complex.exp_ofReal_mul_I_im, Complex.div_ofReal_im] at h
  rw [h, botRow]

variable (g)

def borel (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-g.det / rad g u, (g 1 0 * (g 0 0 + u * g 1 0) + g 1 1 * (g 0 1 + u * g 1 1)) / rad g u; 0, rad g u]

variable {g}

@[scoped simp] theorem borel_apply_10 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 1 0 = 0 := rfl
@[scoped simp] theorem borel_apply_11 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 1 1 = rad g u := rfl
@[scoped simp] theorem borel_apply_00 (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : borel g u 0 0 = -g.det / rad g u := rfl

theorem det_borel (hg : g.det ≠ 0) (u : ℝ) : (borel g u).det = -g.det := by
  rw [borel, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ (rad_pos hg u).ne']

theorem weylUnip_eq_borel_mul_rot (hg : g.det ≠ 0) (u : ℝ) : weylUnip g u = borel g u * rot (angle g u) := by
  have hr : rad g u ≠ 0 := (rad_pos hg u).ne'
  have hr2 := rad_sq g u
  have hD := Matrix.det_fin_two g

  set P : ℝ := g 0 0 + u * g 1 0 with hP
  set Q : ℝ := g 0 1 + u * g 1 1 with hQ
  have hc : Real.cos (angle g u) = Q / rad g u := cos_angle hg u
  have hs : Real.sin (angle g u) = P / rad g u := sin_angle hg u
  have e00 : -g.det / rad g u * (Q / rad g u)
      + (g 1 0 * P + g 1 1 * Q) / rad g u * (P / rad g u) = g 1 0 := by
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_iff (mul_ne_zero hr hr), ← sq, hr2, hD,
      hP, hQ]
    ring
  have e01 : -g.det / rad g u * (-(P / rad g u))
      + (g 1 0 * P + g 1 1 * Q) / rad g u * (Q / rad g u) = g 1 1 := by
    rw [mul_neg, div_mul_div_comm, div_mul_div_comm, ← sub_eq_neg_add, div_sub_div_same,
      div_eq_iff (mul_ne_zero hr hr), ← sq, hr2, hD, hP, hQ]
    ring
  have e10 : (0 : ℝ) * (Q / rad g u) + rad g u * (P / rad g u) = P := by
    rw [zero_mul, zero_add, mul_div_cancel₀ _ hr]
  have e11 : (0 : ℝ) * (-(P / rad g u)) + rad g u * (Q / rad g u) = Q := by
    rw [zero_mul, zero_add, mul_div_cancel₀ _ hr]
  rw [weylUnip_eq, borel, rot, Matrix.mul_fin_two, hc, hs, ← hP, ← hQ, e00, e01, e10, e11]

def borelGL (hg : g.det ≠ 0) (u : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borel g u) (by rw [det_borel hg]; exact neg_ne_zero.2 hg)

@[scoped simp] theorem coe_borelGL (hg : g.det ≠ 0) (u : ℝ) :
    ((borelGL hg u : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = borel g u := rfl

def weylR : GL (Fin 2) ℝ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

def unipR (u : ℝ) : GL (Fin 2) ℝ :=
  ⟨!![1, u; 0, 1], !![1, -u; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem weylR_mul_unipR_mul_eq (g : GL (Fin 2) ℝ) (u : ℝ) :
    weylR * unipR u * g
      = borelGL (g := (g : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.GeneralLinearGroup.det_ne_zero g) u
        * rotGL (angle (g : Matrix (Fin 2) (Fin 2) ℝ) u) := by
  apply Units.ext
  simp only [Units.val_mul, coe_borelGL, coe_rotGL]
  exact weylUnip_eq_borel_mul_rot (Matrix.GeneralLinearGroup.det_ne_zero g) u

def invTower (g : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  (-1) ^ k * (k ! : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ))

theorem invTower_zero (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) : invTower g 0 u = ((u : ℂ) - center g)⁻¹ := by
  simp [invTower]

theorem hasDerivAt_logLine (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (logLine g) (invTower g 0 u) u := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ) - center g) 1 u := (hasDerivAt_id u).ofReal_comp.sub_const _
  have h2 := h.clog_real (sub_center_mem_slitPlane hg u)
  rw [invTower_zero, ← one_div]
  exact h2

theorem hasDerivAt_invTower (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    HasDerivAt (invTower g k) (invTower g (k + 1) u) u := by
  have hz := sub_center_ne_zero hg u
  have h1 : HasDerivAt (fun z : ℂ => (z - center g) ^ (-1 - (k : ℤ)))
      (((-1 - (k : ℤ) : ℤ) : ℂ) * ((u : ℂ) - center g) ^ (-1 - (k : ℤ) - 1)) (u : ℂ) := by
    have := (hasDerivAt_zpow (-1 - (k : ℤ)) ((u : ℂ) - center g) (Or.inl hz)).comp (u : ℂ)
      ((hasDerivAt_id (u : ℂ)).sub_const (center g))
    simp at this ⊢
    exact this
  have h2 := (h1.comp_ofReal).const_mul ((-1) ^ k * (k ! : ℂ))
  refine h2.congr_deriv ?_
  have he : (-1 - (k : ℤ) - 1) = (-1 - ((k + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [invTower, he, Nat.factorial_succ]
  push_cast
  ring

theorem hasDerivAt_im {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).im) F'.im u := by
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

theorem hasDerivAt_re {F : ℝ → ℂ} {F' : ℂ} {u : ℝ} (h : HasDerivAt F F' u) :
    HasDerivAt (fun y => (F y).re) F'.re u := by
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h
  simpa [Function.comp_def] using h2

theorem iteratedDeriv_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (logLine g) = invTower g k := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_logLine hg u).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_invTower hg k u).deriv

theorem iteratedDeriv_im_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).im) = fun u => (invTower g k u).im := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_im (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_im (hasDerivAt_invTower hg k u)).deriv

theorem iteratedDeriv_re_logLine_succ (hg : g.det ≠ 0) (k : ℕ) :
    iteratedDeriv (k + 1) (fun u => (logLine g u).re) = fun u => (invTower g k u).re := by
  induction k with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext u
    exact (hasDerivAt_re (hasDerivAt_logLine hg u)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    exact (hasDerivAt_re (hasDerivAt_invTower hg k u)).deriv

theorem iteratedDeriv_angle_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (angle g) u = (invTower g k u).im := by
  have h : angle g = fun u => Complex.arg (dir g) + (logLine g u).im := rfl
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_im_logLine_succ hg k]

theorem iteratedDeriv_log_rad_succ (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u = (invTower g k u).re := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h, iteratedDeriv_const_add (Nat.succ_pos k), iteratedDeriv_re_logLine_succ hg k]

theorem hasDerivAt_angle (hg : g.det ≠ 0) (u : ℝ) : HasDerivAt (angle g) (-g.det / rad g u ^ 2) u := by
  have h := (hasDerivAt_im (hasDerivAt_logLine hg u)).const_add (Complex.arg (dir g))
  refine h.congr_deriv ?_
  rw [invTower_zero, Complex.inv_im, im_sub_center, rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm, neg_div,
    div_div, neg_div]

theorem hasDerivAt_log_rad (hg : g.det ≠ 0) (u : ℝ) :
    HasDerivAt (fun u => Real.log (rad g u)) (botNormSq g * (u - foot g) / rad g u ^ 2) u := by
  have h := (hasDerivAt_re (hasDerivAt_logLine hg u)).const_add (Real.log ‖dir g‖)
  have hfun : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [hfun]
  refine h.congr_deriv ?_
  have hA : botNormSq g ≠ 0 := (botNormSq_pos hg).ne'
  rw [invTower_zero, Complex.inv_re, re_sub_center, rad_eq hg, mul_pow, norm_dir_sq, Complex.sq_norm,
    mul_div_mul_left _ _ hA]

theorem deriv_angle (hg : g.det ≠ 0) (u : ℝ) : deriv (angle g) u = -g.det / rad g u ^ 2 :=
  (hasDerivAt_angle hg u).deriv

theorem contDiff_logLine (hg : g.det ≠ 0) : ContDiff ℝ ∞ (logLine g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) - center g) u :=
    (Complex.ofRealCLM.contDiff.sub contDiff_const).contDiffAt
  have h2 : ContDiffAt ℝ ∞ Complex.log ((u : ℂ) - center g) :=
    (Complex.contDiffAt_log (sub_center_mem_slitPlane hg u)).restrict_scalars ℝ
  exact h2.comp u h1

theorem contDiff_angle (hg : g.det ≠ 0) : ContDiff ℝ ∞ (angle g) :=
  contDiff_const.add (Complex.imCLM.contDiff.comp (contDiff_logLine hg))

theorem contDiff_log_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (fun u => Real.log (rad g u)) := by
  have h : (fun u => Real.log (rad g u)) = fun u => Real.log ‖dir g‖ + (logLine g u).re :=
    funext (log_rad_eq hg)
  rw [h]
  exact contDiff_const.add (Complex.reCLM.contDiff.comp (contDiff_logLine hg))

theorem contDiff_rad (hg : g.det ≠ 0) : ContDiff ℝ ∞ (rad g) := by
  have h : rad g = fun u => Real.exp (Real.log (rad g u)) :=
    funext fun u => (Real.exp_log (rad_pos hg u)).symm
  rw [h]
  exact Real.contDiff_exp.comp (contDiff_log_rad hg)

theorem contDiff_rot_angle_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun u => rot (angle g u) i j) :=
  (contDiff_rot_apply i j).comp (contDiff_angle hg)

theorem norm_invTower_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    ‖invTower g k u‖ ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  have hz := sub_center_ne_zero hg u
  have hpos : 0 < |g.det| / botNormSq g := div_pos (abs_pos.2 hg) (botNormSq_pos hg)
  have hle := abs_det_div_le_norm_sub_center hg u
  have hk : (-1 - (k : ℤ)) = -(((k + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [invTower, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, hk,
    zpow_neg, zpow_natCast, norm_inv, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc (‖(u : ℂ) - center g‖ ^ (k + 1))⁻¹ ≤ ((|g.det| / botNormSq g) ^ (k + 1))⁻¹ :=
        inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hle _)
    _ = (botNormSq g / |g.det|) ^ (k + 1) := by rw [← inv_pow, inv_div]

theorem abs_iteratedDeriv_angle_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (angle g) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_angle_succ hg]
  exact (Complex.abs_im_le_norm _).trans (norm_invTower_le hg k u)

theorem abs_iteratedDeriv_log_rad_le (hg : g.det ≠ 0) (k : ℕ) (u : ℝ) :
    |iteratedDeriv (k + 1) (fun u => Real.log (rad g u)) u| ≤ k ! * (botNormSq g / |g.det|) ^ (k + 1) := by
  rw [iteratedDeriv_log_rad_succ hg]
  exact (Complex.abs_re_le_norm _).trans (norm_invTower_le hg k u)

theorem center_one : center (1 : Matrix (Fin 2) (Fin 2) ℝ) = -Complex.I := by
  apply Complex.ext <;> simp [center, foot, botNormSq, Matrix.one_apply_ne]

theorem rad_one (u : ℝ) : rad (1 : Matrix (Fin 2) (Fin 2) ℝ) u = ‖(u : ℂ) + Complex.I‖ := by
  rw [rad_eq (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp) u, center_one, sub_neg_eq_add]
  have : dir (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    apply Complex.ext <;> simp [dir, Matrix.one_apply_ne]
  rw [this, norm_one, one_mul]

example (u : ℝ) : Real.cos (angle (1 : Matrix (Fin 2) (Fin 2) ℝ) u) = u / rad (1 : Matrix (Fin 2) (Fin 2) ℝ) u := by
  rw [cos_angle (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp)]
  simp [Matrix.one_apply_ne]

example (u : ℝ) : Real.sin (angle (1 : Matrix (Fin 2) (Fin 2) ℝ) u) = 1 / rad (1 : Matrix (Fin 2) (Fin 2) ℝ) u := by
  rw [sin_angle (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp)]
  simp [Matrix.one_apply_ne]

example (u : ℝ) : deriv (angle (1 : Matrix (Fin 2) (Fin 2) ℝ)) u = -1 / rad (1 : Matrix (Fin 2) (Fin 2) ℝ) u ^ 2 := by
  rw [deriv_angle (g := (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp), Matrix.det_one]

theorem weyl_control_cos : Real.cos (angle !![(0 : ℝ), 1; 1, 0] 0) = 1 := by
  have hg : Matrix.det !![(0 : ℝ), 1; 1, 0] ≠ 0 := by rw [Matrix.det_fin_two_of]; norm_num
  rw [cos_angle hg, rad_eq_sqrt]
  simp

theorem weyl_control_sin : Real.sin (angle !![(0 : ℝ), 1; 1, 0] 0) = 0 := by
  have hg : Matrix.det !![(0 : ℝ), 1; 1, 0] ≠ 0 := by rw [Matrix.det_fin_two_of]; norm_num
  rw [sin_angle hg]
  simp

theorem weyl_control_borel : borel !![(0 : ℝ), 1; 1, 0] 0 = 1 := by
  rw [borel, rad_eq_sqrt, Matrix.det_fin_two_of, Matrix.one_fin_two]
  simp

example : weylUnip !![(0 : ℝ), 1; 1, 0] 0 = 1 := by
  rw [weylUnip_eq, Matrix.one_fin_two]
  simp

end M4aP3B.RealIwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

set_option autoImplicit false

noncomputable section

open MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff

namespace M4aP3B
namespace AutoSmooth

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

structure IsOneParamGroup (R : ℝ → A) : Prop where
  map_zero : R 0 = 1
  map_add : ∀ s t : ℝ, R (s + t) = R s * R t
  continuous : Continuous R

def prim (R : ℝ → A) (t : ℝ) : A := ∫ u in (0 : ℝ)..t, R u

namespace IsOneParamGroup

variable {R : ℝ → A}

theorem hasDerivAt_prim (hR : IsOneParamGroup R) (t : ℝ) : HasDerivAt (prim R) (R t) t :=
  (hR.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim (hR : IsOneParamGroup R) : deriv (prim R) = R :=
  funext fun t => (hR.hasDerivAt_prim t).deriv

theorem differentiable_prim (hR : IsOneParamGroup R) : Differentiable ℝ (prim R) :=
  fun t => (hR.hasDerivAt_prim t).differentiableAt

theorem mul_prim (hR : IsOneParamGroup R) (t ε : ℝ) :
    R t * prim R ε = prim R (t + ε) - prim R t := by
  have h1 : R t * prim R ε = ∫ u in (0 : ℝ)..ε, R t * R u := by
    have h := (ContinuousLinearMap.mul ℝ A (R t)).intervalIntegral_comp_comm
      (hR.continuous.intervalIntegrable (μ := volume) 0 ε)
    simpa [prim] using h.symm
  have h2 : (∫ u in (0 : ℝ)..ε, R t * R u) = ∫ u in (0 : ℝ)..ε, R (t + u) := by
    congr 1
    funext u
    rw [hR.map_add]
  have h3 : (∫ u in (0 : ℝ)..ε, R (t + u)) = ∫ v in t..t + ε, R v := by
    rw [intervalIntegral.integral_comp_add_left R t, add_zero]
  have h4 : prim R (t + ε) - prim R t = ∫ v in t..t + ε, R v := by
    unfold prim
    exact intervalIntegral.integral_interval_sub_left (hR.continuous.intervalIntegrable _ _)
      (hR.continuous.intervalIntegrable _ _)
  rw [h1, h2, h3, h4]

theorem exists_isUnit_prim (hR : IsOneParamGroup R) : ∃ ε : ℝ, 0 < ε ∧ IsUnit (prim R ε) := by
  have hc : ContinuousAt R 0 := hR.continuous.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hball⟩ := hc (1 / 2) (by norm_num)
  have hε0 : (0 : ℝ) < δ / 2 := by positivity
  refine ⟨δ / 2, hε0, ?_⟩
  set ε : ℝ := δ / 2 with hεdef

  have hbound : ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ 1 / 2 * |ε - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hε0.le] at hu
    have hud : dist u 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]
      linarith [hu.2]
    have h := hball hud
    rw [hR.map_zero, dist_eq_norm] at h
    exact h.le
  have hsplit : (∫ u in (0 : ℝ)..ε, (R u - 1)) = prim R ε - ε • (1 : A) := by
    rw [intervalIntegral.integral_sub (hR.continuous.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    rfl

  have hx : ‖(1 : A) - ε⁻¹ • prim R ε‖ < 1 := by
    have hrw : (1 : A) - ε⁻¹ • prim R ε = -(ε⁻¹ • (prim R ε - ε • (1 : A))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hε0.ne', one_smul, neg_sub]
    rw [hrw, norm_neg, norm_smul, ← hsplit, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
    calc ε⁻¹ * ‖∫ u in (0 : ℝ)..ε, (R u - 1)‖ ≤ ε⁻¹ * (1 / 2 * |ε - 0|) := by gcongr
      _ = 1 / 2 := by rw [sub_zero, abs_of_pos hε0]; field_simp
      _ < 1 := by norm_num
  have hu : IsUnit (ε⁻¹ • prim R ε) := by
    have h := (Units.oneSub ((1 : A) - ε⁻¹ • prim R ε) hx).isUnit
    rwa [Units.val_oneSub, sub_sub_cancel] at h
  have hεA : IsUnit (algebraMap ℝ A ε) := (isUnit_iff_ne_zero.2 hε0.ne').map (algebraMap ℝ A)
  have hrw : prim R ε = algebraMap ℝ A ε * (ε⁻¹ • prim R ε) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hε0.ne', one_smul]
  rw [hrw]
  exact hεA.mul hu

theorem eq_sub_mul_inv (hR : IsOneParamGroup R) {ε : ℝ} (u : Aˣ) (hu : (u : A) = prim R ε) (t : ℝ) :
    R t = (prim R (t + ε) - prim R t) * (u⁻¹ : Aˣ) := by
  rw [← hR.mul_prim t ε, ← hu, Units.mul_inv_cancel_right]

theorem contDiff_nat (hR : IsOneParamGroup R) : ∀ n : ℕ, ContDiff ℝ n R := by
  obtain ⟨ε, _hε, hunit⟩ := hR.exists_isUnit_prim
  obtain ⟨u, hu⟩ := hunit
  have hformula : R = fun t => (prim R (t + ε) - prim R t) * ((u⁻¹ : Aˣ) : A) :=
    funext (hR.eq_sub_mul_inv u hu)
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact contDiff_zero.2 hR.continuous
  | succ n ih =>
    have hP : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (prim R) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨hR.differentiable_prim, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
      rw [hR.deriv_prim]
      exact ih
    rw [Nat.cast_succ, hformula]
    exact ((hP.comp (contDiff_id.add contDiff_const)).sub hP).mul contDiff_const

theorem contDiff (hR : IsOneParamGroup R) : ContDiff ℝ ∞ R :=
  contDiff_infty.2 hR.contDiff_nat

theorem differentiable (hR : IsOneParamGroup R) : Differentiable ℝ R :=
  (hR.contDiff_nat 1).differentiable (by simp)

theorem deriv_eq_mul (hR : IsOneParamGroup R) (t : ℝ) : deriv R t = R t * deriv R 0 := by
  have hd := hR.differentiable
  have heq : (fun s => R (t + s)) = fun s => R t * R s := funext fun s => hR.map_add t s
  calc deriv R t = deriv (fun s => R (t + s)) 0 := by rw [deriv_comp_const_add, add_zero]
    _ = deriv (fun s => R t * R s) 0 := by rw [heq]
    _ = R t * deriv R 0 := deriv_const_mul _ (hd 0)

theorem deriv_eq_mul' (hR : IsOneParamGroup R) (t : ℝ) : deriv R t = deriv R 0 * R t := by
  have hd := hR.differentiable
  have heq : (fun s => R (s + t)) = fun s => R s * R t := funext fun s => hR.map_add s t
  calc deriv R t = deriv (fun s => R (s + t)) 0 := by rw [deriv_comp_add_const, zero_add]
    _ = deriv (fun s => R s * R t) 0 := by rw [heq]
    _ = deriv R 0 * R t := deriv_mul_const (hd 0) _

theorem commute_deriv_zero (hR : IsOneParamGroup R) (t : ℝ) : Commute (R t) (deriv R 0) := by
  have h := hR.deriv_eq_mul t
  rw [hR.deriv_eq_mul' t] at h
  exact h.symm

theorem iteratedDeriv_eq (hR : IsOneParamGroup R) (k : ℕ) :
    iteratedDeriv k R = fun t => R t * deriv R 0 ^ k := by
  induction k with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_mul_const (hR.differentiable t), hR.deriv_eq_mul t, mul_assoc, ← pow_succ']

theorem norm_iteratedDeriv_le (hR : IsOneParamGroup R) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k R t‖ ≤ ‖R t‖ * ‖deriv R 0‖ ^ k := by
  rw [hR.iteratedDeriv_eq k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le' _ hk)

theorem norm_iteratedDeriv_le_of_bound (hR : IsOneParamGroup R) {S : Set ℝ} {M : ℝ}
    (hM : ∀ t ∈ S, ‖R t‖ ≤ M) (k : ℕ) (t : ℝ) (ht : t ∈ S) :
    ‖iteratedDeriv k R t‖ ≤ M * ‖deriv R 0‖ ^ k :=
  (hR.norm_iteratedDeriv_le k t).trans (by gcongr; exact hM t ht)

end IsOneParamGroup
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

theorem contDiff_of_continuous_addChar (χ : ℝ → ℂ) (h0 : χ 0 = 1) (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hc : Continuous χ) : ContDiff ℝ ∞ χ :=
  (IsOneParamGroup.mk h0 hadd hc).contDiff

theorem deriv_continuous_addChar (χ : ℝ → ℂ) (h0 : χ 0 = 1) (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hc : Continuous χ) (t : ℝ) : deriv χ t = χ t * deriv χ 0 :=
  (IsOneParamGroup.mk h0 hadd hc).deriv_eq_mul t

example : IsOneParamGroup (fun _ : ℝ => (1 : A)) :=
  ⟨rfl, fun _ _ => (mul_one _).symm, continuous_const⟩

theorem isOneParamGroup_cexp (c : ℂ) : IsOneParamGroup (fun t : ℝ => Complex.exp (t * c)) := by
  refine ⟨by simp, fun s t => ?_, Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)⟩
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem deriv_cexp_zero (c : ℂ) : deriv (fun t : ℝ => Complex.exp (t * c)) 0 = c := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * c))
      (Complex.exp ((((0 : ℝ) : ℂ)) * c) * (1 * c)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' ((0 : ℝ) : ℂ)).mul_const c).cexp
  have h2 := h1.comp_ofReal
  rw [h2.deriv]
  simp

example (c : ℂ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => Complex.exp (t * c)) t = Complex.exp (t * c) * c ^ k := by
  have h := congrFun ((isOneParamGroup_cexp c).iteratedDeriv_eq k) t
  rwa [deriv_cexp_zero] at h

end M4aP3B.AutoSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa M4aP3B.AutoSmooth

namespace M4aP3B
namespace ScalarMajorant

section Constants

variable (g : Matrix (Fin 2) (Fin 2) ℝ)

def towerRatio : ℝ := botNormSq g / |g.det|

def towerD (n : ℕ) : ℝ := n ! * max 1 (towerRatio g)

def radFloor : ℝ := min ((g.det ^ 2 / botNormSq g) / (1 + 2 * foot g ^ 2)) (botNormSq g / 2)

variable {g}

theorem towerRatio_nonneg : 0 ≤ towerRatio g :=
  div_nonneg (by unfold botNormSq; positivity) (abs_nonneg _)

theorem one_le_towerD (n : ℕ) : 1 ≤ towerD g n :=
  one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n) (le_max_left _ _)

theorem towerD_pos (n : ℕ) : 0 < towerD g n := one_pos.trans_le (one_le_towerD n)

theorem radFloor_pos (hg : g.det ≠ 0) : 0 < radFloor g := by
  have hA := botNormSq_pos hg
  unfold radFloor
  exact lt_min (by positivity) (by linarith)

theorem floor_aux {A D f : ℝ} (hA : 0 < A) (hD : 0 < D) (u : ℝ) :
    min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2) ≤ A * (u - f) ^ 2 + D := by
  have h1 : 1 + u ^ 2 ≤ (1 + 2 * f ^ 2) + 2 * (u - f) ^ 2 := by nlinarith [sq_nonneg (u - 2 * f), sq_nonneg f]
  have hf2 : 0 < 1 + 2 * f ^ 2 := by positivity
  have hmin0 : 0 ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) := le_min (div_nonneg hD.le hf2.le) (by linarith)
  calc min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + u ^ 2)
      ≤ min (D / (1 + 2 * f ^ 2)) (A / 2) * ((1 + 2 * f ^ 2) + 2 * (u - f) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hmin0
    _ = min (D / (1 + 2 * f ^ 2)) (A / 2) * (1 + 2 * f ^ 2)
          + min (D / (1 + 2 * f ^ 2)) (A / 2) * (2 * (u - f) ^ 2) := by ring
    _ ≤ D / (1 + 2 * f ^ 2) * (1 + 2 * f ^ 2) + A / 2 * (2 * (u - f) ^ 2) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
    _ = A * (u - f) ^ 2 + D := by
        field_simp
        ring

theorem radFloor_mul_le_rad_sq (hg : g.det ≠ 0) (u : ℝ) : radFloor g * (1 + u ^ 2) ≤ rad g u ^ 2 := by
  rw [rad_sq_eq hg]
  exact floor_aux (botNormSq_pos hg) (by have := botNormSq_pos hg; positivity) u

theorem max_one_abs_sq_le (u : ℝ) : max 1 |u| ^ 2 ≤ 1 + u ^ 2 := by
  rcases le_total 1 |u| with h | h
  · rw [max_eq_right h, sq_abs]; linarith
  · rw [max_eq_left h]; nlinarith [sq_nonneg u]

theorem sqrt_radFloor_mul_le_rad (hg : g.det ≠ 0) (u : ℝ) : Real.sqrt (radFloor g) * max 1 |u| ≤ rad g u := by
  have hc := radFloor_pos hg
  have h2 : (Real.sqrt (radFloor g) * max 1 |u|) ^ 2 ≤ rad g u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact (mul_le_mul_of_nonneg_left (max_one_abs_sq_le u) hc.le).trans (radFloor_mul_le_rad_sq hg u)
  have h3 := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (rad_pos hg u).le] at h3

theorem rad_rpow_neg_le (hg : g.det ≠ 0) {β : ℝ} (hβ : 0 ≤ β) (u : ℝ) :
    rad g u ^ (-β) ≤ Real.sqrt (radFloor g) ^ (-β) * max 1 |u| ^ (-β) := by
  have hpos : 0 < Real.sqrt (radFloor g) * max 1 |u| :=
    mul_pos (Real.sqrt_pos.2 (radFloor_pos hg)) (lt_max_of_lt_left one_pos)
  rw [← Real.mul_rpow (Real.sqrt_nonneg _) (zero_le_one.trans (le_max_left _ _))]
  exact Real.rpow_le_rpow_of_nonpos hpos (sqrt_radFloor_mul_le_rad hg u) (neg_nonpos.2 hβ)

theorem norm_le_rad_rpow (hg : g.det ≠ 0) {Ψ : ℝ → ℂ} {M β : ℝ}
    (hM : ∀ t, ‖Ψ t‖ ≤ M * Real.exp (-β * t)) (u : ℝ) :
    ‖Ψ (Real.log (rad g u))‖ ≤ M * rad g u ^ (-β) := by
  calc ‖Ψ (Real.log (rad g u))‖ ≤ M * Real.exp (-β * Real.log (rad g u)) := hM _
    _ = M * rad g u ^ (-β) := by rw [Real.rpow_def_of_pos (rad_pos hg u), mul_comm (-β)]

end Constants
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

section Towers

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

theorem factorial_mul_pow_le {k n : ℕ} (hkn : k + 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (k ! : ℝ) * r ^ (k + 1) ≤ ((n ! : ℝ) * max 1 r) ^ (k + 1) := by
  have hn1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_pos n
  have h1 : (k ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le (by omega)
  have h2 : (n ! : ℝ) ≤ (n ! : ℝ) ^ (k + 1) := le_self_pow₀ hn1 (Nat.succ_ne_zero k)
  have h3 : r ^ (k + 1) ≤ max 1 r ^ (k + 1) := pow_le_pow_left₀ hr (le_max_right _ _) _
  calc (k ! : ℝ) * r ^ (k + 1) ≤ (n ! : ℝ) ^ (k + 1) * max 1 r ^ (k + 1) :=
        mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
    _ = ((n ! : ℝ) * max 1 r) ^ (k + 1) := (mul_pow _ _ _).symm

theorem norm_iteratedFDeriv_log_rad_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_log_rad_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

theorem norm_iteratedFDeriv_angle_le (hg : g.det ≠ 0) {n i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (angle g) u‖ ≤ towerD g n ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (abs_iteratedDeriv_angle_le hg k u).trans (factorial_mul_pow_le hin towerRatio_nonneg)

end Towers
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

section Composition

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

theorem norm_iteratedFDeriv_comp_log_rad_le (hg : g.det ≠ 0) {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hΨd : ∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j Ψ t‖ ≤ κ ^ j * ‖Ψ t‖)
    {n i : ℕ} (hin : i ≤ n) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u => Ψ (Real.log (rad g u))) u‖
      ≤ n ! * (max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖) * towerD g n ^ n := by
  have hC : ∀ j, j ≤ i → ‖iteratedFDeriv ℝ j Ψ (Real.log (rad g u))‖
      ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by
    intro j hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine (hΨd j _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (pow_le_pow_left₀ hκ (le_max_right 1 κ) j).trans (pow_le_pow_right₀ (le_max_left 1 κ) (hj.trans hin))
  have hD : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j (fun u => Real.log (rad g u)) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hji => norm_iteratedFDeriv_log_rad_le hg hj1 (hji.trans hin) u
  have h := norm_iteratedFDeriv_comp_le (g := Ψ) (f := fun u => Real.log (rad g u)) (n := i)
    hΨ (contDiff_log_rad hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def] at h
  refine h.trans ?_
  have hfac : (i ! : ℝ) ≤ n ! := by exact_mod_cast Nat.factorial_le hin
  have hpow : towerD g n ^ i ≤ towerD g n ^ n := pow_le_pow_right₀ (one_le_towerD n) hin
  have h0 : 0 ≤ max 1 κ ^ n * ‖Ψ (Real.log (rad g u))‖ := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac h0) hpow (pow_nonneg (towerD_pos n).le _) (by positivity)

end Composition
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

end M4aP3B.ScalarMajorant
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

open MeasureTheory Real VectorFourier
open scoped FourierTransform

noncomputable section

namespace M4aP3B
namespace FourierDecay

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem pow_mul_norm_fourierIntegral_le_of_coercive (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

omit [FiniteDimensional ℝ V] [BorelSpace V] in

theorem gate_degenerate (μ : Measure V) [μ.IsAddHaarMeasure] (w : W) :
    ∃ v : V, ‖v‖ ≤ 1 ∧ (0 : ℝ) * ‖w‖ ≤ ‖(0 : V →L[ℝ] W →L[ℝ] ℝ) v w‖ :=
  ⟨0, by simp, by simp⟩

end M4aP3B.FourierDecay
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

set_option autoImplicit false

noncomputable section

open MeasureTheory
open M4aP3B.RealIwasawa M4aP3B.AutoSmooth M4aP3B.ScalarMajorant
open scoped ContDiff FourierTransform Nat

namespace M4aP3C
namespace RealDecay

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

def Ψ (u : ℂ) (t : ℝ) : ℂ := Complex.exp (↑t * (-u))

theorem isOneParamGroup_Ψ (u : ℂ) : IsOneParamGroup (Ψ u) := isOneParamGroup_cexp (-u)

theorem deriv_Ψ_zero (u : ℂ) : deriv (Ψ u) 0 = -u := deriv_cexp_zero (-u)

theorem norm_Ψ (u : ℂ) (t : ℝ) : ‖Ψ u t‖ = Real.exp (-u.re * t) := by
  unfold Ψ
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    zero_mul, sub_zero]
  ring

theorem norm_iteratedDeriv_Ψ_le (u : ℂ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖u‖ ^ j * ‖Ψ u t‖ := by
  have h := (isOneParamGroup_Ψ u).norm_iteratedDeriv_le j t
  rw [deriv_Ψ_zero, norm_neg] at h
  calc ‖iteratedDeriv j (Ψ u) t‖ ≤ ‖Ψ u t‖ * ‖u‖ ^ j := h
    _ = ‖u‖ ^ j * ‖Ψ u t‖ := mul_comm _ _

theorem norm_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ‖Ψ u (Real.log (rad g x))‖ = rad g x ^ (-u.re) := by
  rw [norm_Ψ, Real.rpow_def_of_pos (rad_pos hg x), mul_comm (-u.re)]

theorem weight_eq (hg : g.det ≠ 0) (u : ℂ) (x : ℝ) :
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
      = Ψ u (Real.log (rad g x)) := by
  rw [← rad_eq_sqrt g x]
  have hr := rad_pos hg x
  unfold Ψ
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.ofReal_log hr.le]

theorem weightFun_eq (hg : g.det ≠ 0) (u : ℂ) :
    (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)))
      = fun x => Ψ u (Real.log (rad g x)) :=
  funext (weight_eq hg u)

theorem contDiff_Ψ_log_rad (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞ (fun x => Ψ u (Real.log (rad g x))) :=
  (isOneParamGroup_Ψ u).contDiff.comp (contDiff_log_rad hg)

theorem contDiff_weight (hg : g.det ≠ 0) (u : ℂ) :
    ContDiff ℝ ∞
      (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) := by
  rw [weightFun_eq hg u]
  exact contDiff_Ψ_log_rad hg u

theorem norm_iteratedFDeriv_Ψ_log_rad_le (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by
  have h := norm_iteratedFDeriv_comp_log_rad_le (g := g) hg (Ψ := Ψ u) (isOneParamGroup_Ψ u).contDiff
    (κ := ‖u‖) (norm_nonneg u) (norm_iteratedDeriv_Ψ_le u) (le_refl n) x
  rw [norm_Ψ_log_rad hg u x] at h
  calc ‖iteratedFDeriv ℝ n (fun x => Ψ u (Real.log (rad g x))) x‖
      ≤ n ! * (max 1 ‖u‖ ^ n * rad g x ^ (-u.re)) * towerD g n ^ n := h
    _ = (n ! * max 1 ‖u‖ ^ n * towerD g n ^ n) * rad g x ^ (-u.re) := by ring

theorem exists_bound_iteratedFDeriv_weight (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        ≤ C * rad g x ^ (-u.re) := by
  refine ⟨n ! * max 1 ‖u‖ ^ n * towerD g n ^ n, ?_, fun x => ?_⟩
  · have h1 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    have h2 : (0 : ℝ) < max 1 ‖u‖ ^ n := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) n
    exact mul_pos (mul_pos h1 h2) (pow_pos (towerD_pos n) n)
  · rw [weightFun_eq hg u]
    exact norm_iteratedFDeriv_Ψ_log_rad_le hg u n x

theorem rad_rpow_neg_le_one_add_sq (hg : g.det ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    rad g x ^ (-κ) ≤ radFloor g ^ (-κ / 2) * (1 + ‖x‖ ^ 2) ^ (-κ / 2) := by
  have hF := radFloor_pos hg
  have hr := rad_pos hg x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2]
  have h1 : rad g x ^ (-κ) = (rad g x ^ 2) ^ (-κ / 2) := by
    rw [← Real.rpow_natCast (rad g x) 2, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  rw [h1, ← Real.mul_rpow hF.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (radFloor_mul_le_rad_sq hg x) (by linarith)

theorem integrable_rpow_neg_rad (hg : g.det ≠ 0) {κ : ℝ} (hκ : 1 < κ) :
    Integrable (fun x => rad g x ^ (-κ)) (volume : Measure ℝ) := by
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-κ / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (μ := volume) (by rw [Module.finrank_self]; exact_mod_cast hκ)
  refine (hint.const_mul (radFloor g ^ (-κ / 2))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((contDiff_rad hg).continuous.rpow_const fun x => Or.inl (rad_pos hg x).ne').aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (rad_pos hg x).le _)]
    exact rad_rpow_neg_le_one_add_sq hg (by linarith) x

theorem exists_bound_iteratedFDeriv_weight_mul (hg : g.det ≠ 0) (u : ℂ)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n
          (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))
            * P x) x‖
        ≤ C * rad g x ^ (-u.re) := by
  intro n
  choose Cf hCf using fun i => exists_bound_iteratedFDeriv_weight hg u i
  choose Ch hCh using hPB
  have hpos : (0:ℝ) < ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Ch (n - i) := by
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
    have h1 : (0:ℝ) < (n.choose i : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    exact mul_pos (mul_pos h1 (hCf i).1) (hCh (n - i)).1
  refine ⟨_, hpos, fun x => ?_⟩
  have hrad := rad_pos hg x
  refine (norm_iteratedFDeriv_mul_le (contDiff_weight hg u) hPC x
    (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  calc (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i
            (fun x : ℝ => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u))) x‖
        * ‖iteratedFDeriv ℝ (n - i) P x‖
      ≤ (n.choose i : ℝ) * (Cf i * rad g x ^ (-u.re)) * Ch (n - i) := by
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCf i).1.le (Real.rpow_nonneg hrad.le _))
        · exact (hCf i).2 x
        · exact (hCh (n - i)).2 x
    _ = (n.choose i : ℝ) * Cf i * Ch (n - i) * rad g x ^ (-u.re) := by ring

theorem norm_fourierIntegral_cpow_radR_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  set f : ℝ → ℂ := fun x =>
    ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x with hfdef

  obtain ⟨CB, hCB⟩ := Classical.axiom_of_choice
    (fun n => exists_bound_iteratedFDeriv_weight_mul hg u hPC hPB n)
  have hintr : Integrable (fun x => rad g x ^ (-u.re)) volume :=
    integrable_rpow_neg_rad hg hu
  have hfC : ContDiff ℝ ∞ f := (contDiff_weight hg u).mul hPC
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (CB j)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (hCB j).2 x

  have key := M4aP3B.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L
    (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume
  have hMN0 : (0:ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)

  have hfint : Integrable f volume := by
    refine (hintr.const_mul (CB 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 := (hCB 0).2 x
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume
  have hM00 : (0:ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  refine ⟨(M0 * 2 ^ N + MN * (2 / c) ^ N) + 1, by positivity, fun ξ => ?_⟩
  have hξ0 : (0:ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0:ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0:ℝ) < (1 + ‖ξ‖) ^ (-(N:ℝ)) := Real.rpow_pos_of_pos h1ξ _
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  ·
    have hbd : (2:ℝ) ^ (-(N:ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith)
        (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0 : ℝ) = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := by
      rw [mul_assoc, show ((2:ℝ)^N : ℝ) = (2:ℝ)^(N:ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ))
        ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hbd
        (mul_nonneg hM00 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0 * 2 ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hMN0
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0 := hstep1
      _ = M0 * 2 ^ N * (2:ℝ) ^ (-(N:ℝ)) := hstep2
      _ ≤ M0 * 2 ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := hstep3
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  ·
    have hkey := key ξ
    have hcξ : (0:ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv,
        le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1:ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N:ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N:ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast,
          ← inv_pow, inv_div]
      rw [hp1]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hc.le) N)
      exact Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep4 : (MN * (2 / c) ^ N : ℝ) ≤ M0 * 2 ^ N + MN * (2 / c) ^ N + 1 := by
      nlinarith [mul_nonneg hM00 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) N)]
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N:ℝ)) := hdiv
      _ ≤ MN * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ))) :=
          mul_le_mul_of_nonneg_left hcmp hMN0
      _ = MN * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N:ℝ)) := by ring
      _ ≤ (M0 * 2 ^ N + MN * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N:ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

theorem radR_eq_rad (g : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) = M4aP3B.RealIwasawa.rad g x :=
  (M4aP3B.RealIwasawa.rad_eq_sqrt g x).symm

theorem radR_control (x : ℝ) :
    Real.sqrt (((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
        + ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2)
      = Real.sqrt ((1 + x * 3) ^ 2 + (2 + x * 4) ^ 2) := by
  simp

theorem hypotheses_inhabited :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 ∧ 1 < (2 : ℂ).re ∧ ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℂ)) ∧
    (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n (fun _ : ℝ => (1 : ℂ)) x‖ ≤ C) ∧
    (0 : ℝ) < 1 ∧
    (∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ 1 * ‖ξ‖ ≤ ‖ContinuousLinearMap.mul ℝ ℝ v ξ‖) := by
  refine ⟨by simp, by norm_num, contDiff_const, fun n => ⟨1, one_pos, fun x => ?_⟩, one_pos, fun ξ => ⟨1, by simp, by simp⟩⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [iteratedFDeriv_const_of_ne hn]
    simp

example (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
    ‖VectorFourier.fourierIntegral 𝐞 volume (ContinuousLinearMap.mul ℝ ℝ).toLinearMap₁₂
        (fun x => ((Real.sqrt (((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2
            + ((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + x * (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℂ) ^ (-(2 : ℂ)))
            * (fun _ : ℝ => (1 : ℂ)) x) ξ‖
      ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  norm_fourierIntegral_cpow_radR_mul_le_polyDecay hypotheses_inhabited.1 hypotheses_inhabited.2.1
    hypotheses_inhabited.2.2.1 hypotheses_inhabited.2.2.2.1 (ContinuousLinearMap.mul ℝ ℝ) hypotheses_inhabited.2.2.2.2.1
    hypotheses_inhabited.2.2.2.2.2 N

end M4aP3C.RealDecay
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.M4aP3B.RealIwasawa"

open MeasureTheory
open scoped ContDiff FourierTransform

theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
  M4aP3C.RealDecay.norm_fourierIntegral_cpow_radR_mul_le_polyDecay hg hu hPC hPB L hc hL N

end S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay
end P2MW
export P2MW.S_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay (solution)
