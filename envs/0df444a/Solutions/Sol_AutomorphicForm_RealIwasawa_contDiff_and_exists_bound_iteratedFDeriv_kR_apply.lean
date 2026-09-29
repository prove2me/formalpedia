-- Prove2me | solution 1 for AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8a3fbaa8-2b49-5bf8-bdf5-27845020324f

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply

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
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa

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
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

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
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

end M4aP3B.ScalarMajorant
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

noncomputable section

open scoped ContDiff Nat
open M4aP3B.RealIwasawa M4aP3B.ScalarMajorant

namespace M4aP3C
namespace RealKTower

variable {g : Matrix (Fin 2) (Fin 2) ℝ}

theorem norm_iteratedFDeriv_comp_angle_le_of_abs_le_one (hg : g.det ≠ 0) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcb : ∀ (j : ℕ) (θ : ℝ), |iteratedDeriv j c θ| ≤ 1) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => c (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hC : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j c (angle g u)‖ ≤ 1 := by
    intro j _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hcb j _
  have hD : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j (angle g) u‖ ≤ towerD g n ^ j :=
    fun j hj1 hjn => norm_iteratedFDeriv_angle_le hg hj1 hjn u
  have h := norm_iteratedFDeriv_comp_le (g := c) (f := angle g) (n := n)
    hc (contDiff_angle hg) (by exact_mod_cast le_top) u hC hD
  rw [Function.comp_def, mul_one] at h
  exact h

theorem norm_iteratedFDeriv_cos_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.cos (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one n u

theorem norm_iteratedFDeriv_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n :=
  norm_iteratedFDeriv_comp_angle_le_of_abs_le_one hg Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one n u

theorem norm_iteratedFDeriv_neg_sin_angle_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ n (fun u => -Real.sin (angle g u)) u‖ ≤ n ! * towerD g n ^ n := by
  have hneg : (fun u => -Real.sin (angle g u)) = -(fun u => Real.sin (angle g u)) := rfl
  rw [hneg, iteratedFDeriv_neg_apply, norm_neg]
  exact norm_iteratedFDeriv_sin_angle_le hg n u

theorem norm_iteratedFDeriv_rot_angle_apply_le (hg : g.det ≠ 0) (n : ℕ) (u : ℝ) :
    ∀ i j : Fin 2, ‖iteratedFDeriv ℝ n (fun x => rot (angle g x) i j) u‖ ≤ n ! * towerD g n ^ n := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact norm_iteratedFDeriv_cos_angle_le hg n u
  · exact norm_iteratedFDeriv_neg_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_sin_angle_le hg n u
  · exact norm_iteratedFDeriv_cos_angle_le hg n u

theorem kR_literal_eq_rot_angle (hg : g.det ≠ 0) : ∀ i j : Fin 2,
    (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)
      = fun x => rot (angle g x) i j := by
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 0 0
    rw [rot_apply_00, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (-(g 0 0 + x * g 1 0))
      = rot (angle g x) 0 1
    rw [rot_apply_01, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul, mul_neg]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 0 + x * g 1 0)
      = rot (angle g x) 1 0
    rw [rot_apply_10, sin_angle hg, rad_eq_sqrt, div_eq_inv_mul]
  · funext x
    show (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹ * (g 0 1 + x * g 1 1)
      = rot (angle g x) 1 1
    rw [rot_apply_11, cos_angle hg, rad_eq_sqrt, div_eq_inv_mul]

theorem contDiff_and_exists_bound (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C := by
  refine ⟨fun i j => ?_, fun n => ⟨n ! * towerD g n ^ n,
    mul_pos (by exact_mod_cast Nat.factorial_pos n) (pow_pos (towerD_pos n) n), fun i j u => ?_⟩⟩
  · rw [kR_literal_eq_rot_angle hg i j]
    exact contDiff_rot_angle_apply hg i j
  · rw [kR_literal_eq_rot_angle hg i j]
    exact norm_iteratedFDeriv_rot_angle_apply_le hg n u i j

end M4aP3C.RealKTower
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

noncomputable section

open scoped ContDiff

theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (u : ℝ),
      ‖iteratedFDeriv ℝ n (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) u‖ ≤ C :=
  M4aP3C.RealKTower.contDiff_and_exists_bound hg

end
p2m_reactivate "P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply.M4aP3B.RealIwasawa"

#print axioms solution

end S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply
end P2MW
export P2MW.S_AutomorphicForm_RealIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kR_apply (solution)
