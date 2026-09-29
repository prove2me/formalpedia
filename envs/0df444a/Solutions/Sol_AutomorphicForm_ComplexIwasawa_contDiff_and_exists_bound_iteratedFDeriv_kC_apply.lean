-- Prove2me | solution 1 for AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9f35f03a-18c4-5a5a-8e53-b2b81d5a3de0

import Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply

set_option autoImplicit false

noncomputable section

open ComplexConjugate
open scoped ContDiff

namespace M4aP3C
namespace CplxIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def weylUnipC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] * !![1, z; 0, 1] * g

def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

def botNormSqC : ℝ := Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def centerC : ℂ := -(conj (g 1 0) * g 0 0 + conj (g 1 1) * g 0 1) / (botNormSqC g : ℂ)

def radC (z : ℂ) : ℝ := Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

def borelC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-g.det / (radC g z : ℂ),
     (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
     0, (radC g z : ℂ)]

variable {g}

theorem radC_sq (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

theorem weylUnipC_eq (z : ℂ) :
    weylUnipC g z = !![g 1 0, g 1 1; g 0 0 + z * g 1 0, g 0 1 + z * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylUnipC, Matrix.mul_apply, Fin.sum_univ_two]

theorem botNormSqC_pos (hg : g.det ≠ 0) : 0 < botNormSqC g := by
  rw [botNormSqC]
  rcases (add_nonneg (Complex.normSq_nonneg (g 1 0)) (Complex.normSq_nonneg (g 1 1))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hc : Complex.normSq (g 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    have hd : Complex.normSq (g 1 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (g 1 0), Complex.normSq_nonneg (g 1 1)]
    apply hg
    rw [Matrix.det_fin_two, Complex.normSq_eq_zero.1 hc, Complex.normSq_eq_zero.1 hd,
      mul_zero, mul_zero, sub_zero]

theorem radC_sq_eq (hg : g.det ≠ 0) (z : ℂ) :
    radC g z ^ 2 = botNormSqC g * Complex.normSq (z - centerC g)
      + Complex.normSq g.det / botNormSqC g := by
  have hA : botNormSqC g ≠ 0 := (botNormSqC_pos hg).ne'
  have hAc : (botNormSqC g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hA
  have hz : z - centerC g = ((botNormSqC g : ℂ) * z + ((starRingEnd ℂ) (g 1 0) * g 0 0
      + (starRingEnd ℂ) (g 1 1) * g 0 1)) / (botNormSqC g : ℂ) := by
    rw [centerC]
    field_simp
    try ring
  rw [radC_sq, hz, Complex.normSq_div, Complex.normSq_ofReal, Matrix.det_fin_two]
  field_simp
  simp only [botP, botQ, botNormSqC, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

theorem radC_pos (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

theorem norm_det_div_sqrt_le_radC (hg : g.det ≠ 0) (z : ℂ) :
    ‖g.det‖ / Real.sqrt (botNormSqC g) ≤ radC g z := by
  have hA := botNormSqC_pos hg
  have hd : 0 ≤ ‖g.det‖ / Real.sqrt (botNormSqC g) := by positivity
  have hsq : (‖g.det‖ / Real.sqrt (botNormSqC g)) ^ 2 ≤ radC g z ^ 2 := by
    rw [div_pow, Real.sq_sqrt hA.le, Complex.sq_norm, radC_sq_eq hg z]
    have h2 : 0 ≤ botNormSqC g * Complex.normSq (z - centerC g) :=
      mul_nonneg (botNormSqC_pos hg).le (Complex.normSq_nonneg _)
    linarith
  calc ‖g.det‖ / Real.sqrt (botNormSqC g)
      = Real.sqrt ((‖g.det‖ / Real.sqrt (botNormSqC g)) ^ 2) := (Real.sqrt_sq hd).symm
    _ ≤ Real.sqrt (radC g z ^ 2) := Real.sqrt_le_sqrt hsq
    _ = radC g z := Real.sqrt_sq (radC_pos hg z).le

theorem kC_mul_conjTranspose (hg : g.det ≠ 0) (z : ℂ) :
    kC g z * (kC g z).conjTranspose = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

theorem conjTranspose_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

theorem det_kC (hg : g.det ≠ 0) (z : ℂ) : (kC g z).det = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have e : (kC g z).det = (botQ g z * (starRingEnd ℂ) (botQ g z)
      + botP g z * (starRingEnd ℂ) (botP g z)) / ((radC g z : ℂ) * (radC g z : ℂ)) := by
    rw [kC, Matrix.det_fin_two_of]
    ring
  have num : ((Complex.normSq (botQ g z) + Complex.normSq (botP g z) : ℝ) : ℂ)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  rw [e, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, num,
    div_self (mul_ne_zero hr hr)]

theorem det_borelC (hg : g.det ≠ 0) (z : ℂ) : (borelC g z).det = -g.det := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  rw [borelC, Matrix.det_fin_two_of, mul_zero, sub_zero, div_mul_cancel₀ _ hr]

theorem weylUnipC_eq_borelC_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    weylUnipC g z = borelC g z * kC g z := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos hg z).ne'
  have key : botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq g z]
  simp only [botP, botQ, map_add, map_mul] at key
  rw [weylUnipC_eq, borelC, kC, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, botP, botQ, map_add, map_mul] <;>
    (try field_simp) <;>
    first
    | (rw [pow_two ((radC g z : ℂ)), ← key]
       ring)
    | ring

theorem norm_row_sq_kC (hg : g.det ≠ 0) (z : ℂ) (x y : ℂ) :
    ‖x * kC g z 0 0 + y * kC g z 1 0‖ ^ 2 + ‖x * kC g z 0 1 + y * kC g z 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have hrr : radC g z * radC g z = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
    rw [← pow_two]
    exact radC_sq g z
  have e1 : x * kC g z 0 0 + y * kC g z 1 0
      = (x * (starRingEnd ℂ) (botQ g z) + y * botP g z) / (radC g z : ℂ) := by
    simp [kC]
    try ring
  have e2 : x * kC g z 0 1 + y * kC g z 1 1
      = (-(x * (starRingEnd ℂ) (botP g z)) + y * botQ g z) / (radC g z : ℂ) := by
    simp [kC]
    try ring
  rw [e1, e2]
  simp only [Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal]
  rw [← add_div, hrr]
  have hpos : 0 < Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
    rw [← radC_sq g z]
    exact pow_pos (radC_pos hg z) 2
  rw [div_eq_iff hpos.ne']
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

theorem contDiff_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ (radC g) := by
  have hnormSq : ContDiff ℝ ∞ Complex.normSq := by
    have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
      funext w
      exact Complex.normSq_apply w
    rw [h]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hinner : ContDiff ℝ ∞ (fun z => Complex.normSq (botP g z) + Complex.normSq (botQ g z)) :=
    (hnormSq.comp hP).add (hnormSq.comp hQ)
  rw [contDiff_iff_contDiffAt]
  intro z
  have hpos : Complex.normSq (botP g z) + Complex.normSq (botQ g z) ≠ 0 := by
    rw [← radC_sq g z]
    exact (pow_pos (radC_pos hg z) 2).ne'
  have h := (Real.contDiffAt_sqrt hpos).comp z hinner.contDiffAt
  simp [radC, Function.comp_def] at h
  exact h

theorem contDiff_kC_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun z => kC g z i j) := by
  have hradInv : ContDiff ℝ ∞ (fun z => (radC g z)⁻¹) :=
    (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'
  have hradInvC : ContDiff ℝ ∞ (fun z => (((radC g z)⁻¹ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hradInv
  have hconj : ContDiff ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) := Complex.conjCLE.contDiff
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hPc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botP g z)) := hconj.comp hP
  have hQc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botQ g z)) := hconj.comp hQ
  have hdiv : ∀ (w : ℂ) (r : ℝ), w / (r : ℂ) = w * ((r⁻¹ : ℝ) : ℂ) := by
    intro w r
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  fin_cases i <;> fin_cases j <;>
    simp only [kC, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    simp only [hdiv, neg_div]
  · exact hQc.mul hradInvC
  · first
    | exact (hPc.mul hradInvC).neg
    | exact hPc.neg.mul hradInvC
  · exact hP.mul hradInvC
  · exact hQ.mul hradInvC

theorem contDiff_borelC_apply (hg : g.det ≠ 0) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun z => borelC g z i j) := by
  have hradC : ContDiff ℝ ∞ (fun z => ((radC g z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_radC hg)
  have hradInv : ContDiff ℝ ∞ (fun z => (radC g z)⁻¹) :=
    (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'
  have hradInvC : ContDiff ℝ ∞ (fun z => (((radC g z)⁻¹ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hradInv
  have hconj : ContDiff ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) := Complex.conjCLE.contDiff
  have hP : ContDiff ℝ ∞ (botP g) := by
    unfold botP
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hQ : ContDiff ℝ ∞ (botQ g) := by
    unfold botQ
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hPc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botP g z)) := hconj.comp hP
  have hQc : ContDiff ℝ ∞ (fun z => (starRingEnd ℂ) (botQ g z)) := hconj.comp hQ
  have hdiv : ∀ (w : ℂ) (r : ℝ), w / (r : ℂ) = w * ((r⁻¹ : ℝ) : ℂ) := by
    intro w r
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  fin_cases i <;> fin_cases j <;>
    simp only [borelC, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] <;>
    simp only [hdiv, neg_div]
  · first
    | exact (contDiff_const.mul hradInvC).neg
    | exact contDiff_const.mul hradInvC
  · exact ((contDiff_const.mul hPc).add (contDiff_const.mul hQc)).mul hradInvC
  · exact contDiff_const
  · exact hradC

def kCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨kC g z, (kC g z).conjTranspose, kC_mul_conjTranspose hg z, conjTranspose_mul_kC hg z⟩

@[scoped simp] theorem coe_kCGL (hg : g.det ≠ 0) (z : ℂ) :
    ((kCGL hg z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = kC g z := rfl

def borelCGL (hg : g.det ≠ 0) (z : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (borelC g z)
    (by rw [det_borelC hg z]; exact neg_ne_zero.2 hg)

@[scoped simp] theorem coe_borelCGL (hg : g.det ≠ 0) (z : ℂ) :
    ((borelCGL hg z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = borelC g z := rfl

def weylC : GL (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

def unipC (z : ℂ) : GL (Fin 2) ℂ :=
  ⟨!![1, z; 0, 1], !![1, -z; 0, 1],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem weylC_mul_unipC_mul_eq (g : GL (Fin 2) ℂ) (z : ℂ) :
    weylC * unipC z * g
      = borelCGL (g := (g : Matrix (Fin 2) (Fin 2) ℂ))
          (Matrix.GeneralLinearGroup.det_ne_zero g) z
        * kCGL (Matrix.GeneralLinearGroup.det_ne_zero g) z := by
  apply Units.ext
  simp only [Units.val_mul, coe_borelCGL, coe_kCGL]
  exact weylUnipC_eq_borelC_mul_kC (Matrix.GeneralLinearGroup.det_ne_zero g) z

theorem ctrl_weylUnipC_w : weylUnipC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [weylUnipC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ctrl_radC_w : radC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

theorem ctrl_kC_w : kC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [kC, Matrix.one_fin_two, ctrl_radC_w, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem ctrl_borelC_w : borelC !![(0 : ℂ), 1; 1, 0] 0 = 1 := by
  rw [borelC, Matrix.one_fin_two, ctrl_radC_w, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of]

theorem ctrl_radC_c1 : radC !![Complex.I, 0; 0, 1] 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

theorem ctrl_decomp_c1 :
    weylUnipC !![Complex.I, 0; 0, 1] 0
      = borelC !![Complex.I, 0; 0, 1] 0 * kC !![Complex.I, 0; 0, 1] 0 := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c1, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of]

theorem ctrl_radC_c2 : radC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) = 3 := by
  rw [radC, show (3 : ℝ) = Real.sqrt 9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

theorem ctrl_decomp_c2 :
    weylUnipC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)
      = borelC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) * kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I) := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c2, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of, Complex.ext_iff] <;>
    norm_num

theorem ctrl_radC_c3 : radC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) = 3 := by
  rw [radC, show (3 : ℝ) = Real.sqrt 9 by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply]

theorem ctrl_decomp_c3 :
    weylUnipC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I)
      = borelC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) * kC !![(0 : ℂ), 1; 2, 0] (1 + Complex.I) := by
  rw [weylUnipC, borelC, kC, ctrl_radC_c3, botP, botQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two_of, Complex.ext_iff] <;>
    norm_num

theorem ctrl_kC_unitary_c2 :
    kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)
      * (kC !![(1 : ℂ), 0; 0, 2] (1 + Complex.I)).conjTranspose = 1 := by
  rw [kC, ctrl_radC_c2, botP, botQ, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat,
      Complex.ext_iff] <;>
    norm_num

end M4aP3C.CplxIwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C"

end
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa"

noncomputable section

namespace M4aP3C
namespace CplxSmooth

open scoped ContDiff Nat

open M4aP3C.CplxIwasawa

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

theorem ctrl_radC_one_zero : radC (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 1 := by
  rw [radC, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  congr 1
  norm_num [botP, botQ, Complex.normSq_apply, Matrix.one_apply]

theorem ctrl_kC_one_zero :
    kC (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = !![0, -1; 1, 0] := by
  rw [kC, ctrl_radC_one_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [botP, botQ, Matrix.one_apply]

theorem ctrl_fderiv_botQ_one (z : ℂ) :
    fderiv ℝ (botQ (1 : Matrix (Fin 2) (Fin 2) ℂ)) z = ContinuousLinearMap.id ℝ ℂ := by
  have h : botQ (1 : Matrix (Fin 2) (Fin 2) ℂ) = id := by
    funext w
    simp [botQ, Matrix.one_apply]
  rw [h, fderiv_id]

theorem iteratedDerivWithin_rpow_const {c : ℝ} (hc : 0 < c) (r : ℝ) (k : ℕ) :
    Set.EqOn (iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c))
      (fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k)) (Set.Ioi c) := by
  induction k with
  | zero =>
    intro v hv
    simp [iteratedDerivWithin_zero]
  | succ k ih =>
    intro v hv
    have hvpos : 0 < v := hc.trans hv
    have hopen : IsOpen (Set.Ioi c) := isOpen_Ioi
    rw [iteratedDerivWithin_succ, derivWithin_of_isOpen hopen hv]
    have hev : iteratedDerivWithin k (fun v : ℝ => v ^ r) (Set.Ioi c)
        =ᶠ[nhds v] fun v => (∏ i ∈ Finset.range k, (r - i)) * v ^ (r - k) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun v : ℝ => v ^ (r - k))
        ((r - k) * v ^ (r - k - 1)) v :=
      Real.hasDerivAt_rpow_const (Or.inl hvpos.ne')
    rw [deriv_const_mul _ hd.differentiableAt, hd.deriv]
    rw [Finset.prod_range_succ]
    push_cast
    ring_nf

theorem norm_iteratedDerivWithin_rpow_neg_half_le {c : ℝ} (hc : 0 < c) (k : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) (Set.Ioi c) v‖
      ≤ k ! * c ^ (-(1 : ℝ) / 2 - k) := by
  have hvpos : (0 : ℝ) < v := hc.trans hv
  rw [iteratedDerivWithin_rpow_const hc (-(1 : ℝ) / 2) k hv]
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| ≤ (k ! : ℝ) := by
    rw [Finset.abs_prod]
    have hfac : (k ! : ℝ) = ∏ i ∈ Finset.range k, ((i : ℝ) + 1) := by
      induction k with
      | zero => simp
      | succ n ih => rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hneg : (-(1 : ℝ) / 2 - i) < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have h2 : |v ^ (-(1 : ℝ) / 2 - (k : ℝ))| ≤ c ^ (-(1 : ℝ) / 2 - k) := by
    rw [abs_of_nonneg (Real.rpow_nonneg hvpos.le _)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
      (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hvpos) hv.le
  calc |∏ i ∈ Finset.range k, (-(1 : ℝ) / 2 - i)| * |v ^ (-(1 : ℝ) / 2 - (k : ℝ))|
      ≤ (k ! : ℝ) * c ^ (-(1 : ℝ) / 2 - k) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

def uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ → ℝ := fun w =>
  botNormSqC g * Complex.normSq (w - centerC g) + Complex.normSq g.det / botNormSqC g

theorem uQuad_eq_radC_sq (hg : g.det ≠ 0) (w : ℂ) : uQuad g w = radC g w ^ 2 :=
  (radC_sq_eq hg w).symm

theorem uQuad_ge (hg : g.det ≠ 0) (w : ℂ) :
    Complex.normSq g.det / botNormSqC g ≤ uQuad g w := by
  have h : 0 ≤ botNormSqC g * Complex.normSq (w - centerC g) :=
    mul_nonneg (botNormSqC_pos hg).le (Complex.normSq_nonneg _)
  unfold uQuad
  linarith

theorem uQuad_eq_coords (w : ℂ) :
    uQuad g w = botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
      + Complex.normSq g.det / botNormSqC g := by
  unfold uQuad
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem hasFDerivAt_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) :
    HasFDerivAt (uQuad g)
      ((2 * botNormSqC g * (w - centerC g).re) • Complex.reCLM
        + (2 * botNormSqC g * (w - centerC g).im) • Complex.imCLM) w := by
  have hre : HasFDerivAt (fun v : ℂ => (v.re - (centerC g).re) ^ 2)
      ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.re - (centerC g).re)
        (Complex.reCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.reCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have him : HasFDerivAt (fun v : ℂ => (v.im - (centerC g).im) ^ 2)
      ((2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
    have h1 : HasFDerivAt (fun v : ℂ => v.im - (centerC g).im)
        (Complex.imCLM : ℂ →L[ℝ] ℝ) w :=
      (Complex.imCLM.hasFDerivAt).sub_const _
    simpa [pow_one, mul_comm, mul_assoc, smul_smul] using h1.pow 2
  have hsum := ((hre.add him).const_mul (botNormSqC g)).add_const
    (Complex.normSq g.det / botNormSqC g)
  have huq : HasFDerivAt (uQuad g)
      (botNormSqC g • ((2 * (w.re - (centerC g).re)) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * (w.im - (centerC g).im)) • (Complex.imCLM : ℂ →L[ℝ] ℝ))) w := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards with v
    rw [uQuad_eq_coords]
    simp only [Pi.add_apply]
  convert huq using 1
  ext v
  simp [ContinuousLinearMap.smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

def lamQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight ((2 * botNormSqC g) • (Complex.reCLM : ℂ →L[ℝ] ℝ))
    + Complex.imCLM.smulRight ((2 * botNormSqC g) • (Complex.imCLM : ℂ →L[ℝ] ℝ))

@[scoped simp] theorem lamQuad_apply_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (v w : ℂ) :
    lamQuad g v w = 2 * botNormSqC g * v.re * w.re + 2 * botNormSqC g * v.im * w.im := by
  simp [lamQuad, ContinuousLinearMap.smulRight_apply]
  ring

theorem norm_lamQuad_apply_le (g : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) :
    ‖lamQuad g v‖ ≤ 4 * botNormSqC g * ‖v‖ := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hA) (norm_nonneg v)) fun w => ?_
  rw [lamQuad_apply_apply, Real.norm_eq_abs]
  have hre : |v.re * w.re| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm v) (Complex.abs_re_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have him : |v.im * w.im| ≤ ‖v‖ * ‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_im_le_norm v) (Complex.abs_im_le_norm w)
      (abs_nonneg _) (norm_nonneg _)
  have hre' := abs_le.1 hre
  have him' := abs_le.1 him
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left hre'.2 hA, mul_le_mul_of_nonneg_left hre'.1 hA,
      mul_le_mul_of_nonneg_left him'.2 hA, mul_le_mul_of_nonneg_left him'.1 hA]

theorem norm_lamQuad_le (g : Matrix (Fin 2) (Fin 2) ℂ) : ‖lamQuad g‖ ≤ 4 * botNormSqC g := by
  have hA : 0 ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hA)
    fun v => norm_lamQuad_apply_le g v

theorem fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    fderiv ℝ (uQuad g) z = lamQuad g (z - centerC g) := by
  rw [(hasFDerivAt_uQuad g z).fderiv]
  ext w
  simp [ContinuousLinearMap.smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.sub_re, Complex.sub_im]
  ring

theorem hasFDerivAt_fderiv_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    HasFDerivAt (fderiv ℝ (uQuad g)) (lamQuad g) z := by
  have heq : fderiv ℝ (uQuad g) = fun w => lamQuad g (w - centerC g) :=
    funext (fderiv_uQuad g)
  rw [heq]
  have hcomp := (lamQuad g).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (centerC g))
  exact hcomp

theorem norm_iteratedFDeriv_uQuad_one (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * ‖z - centerC g‖ := by
  have h1 : ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  rw [h1, norm_iteratedFDeriv_zero, fderiv_uQuad]
  exact norm_lamQuad_apply_le g _

theorem norm_iteratedFDeriv_uQuad_two (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 (uQuad g) z‖ ≤ 4 * botNormSqC g := by
  have h2 : ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
      = ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 1)).symm
  have h1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := 0)).symm
  have hfd : fderiv ℝ (fderiv ℝ (uQuad g)) z = lamQuad g :=
    (hasFDerivAt_fderiv_uQuad g z).fderiv
  rw [h2, h1, norm_iteratedFDeriv_zero, hfd]
  exact norm_lamQuad_le g

theorem norm_iteratedFDeriv_uQuad_ge_three (g : Matrix (Fin 2) (Fin 2) ℂ) {i : ℕ}
    (hi : 3 ≤ i) (z : ℂ) : ‖iteratedFDeriv ℝ i (uQuad g) z‖ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have hfd2 : fderiv ℝ (fderiv ℝ (uQuad g)) = fun _ => lamQuad g :=
    funext fun w => (hasFDerivAt_fderiv_uQuad g w).fderiv
  have h3 : ‖iteratedFDeriv ℝ (k + 3) (uQuad g) z‖
      = ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 2)).symm
  have h4 : ‖iteratedFDeriv ℝ (k + 2) (fderiv ℝ (uQuad g)) z‖
      = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ (fderiv ℝ (uQuad g))) z‖ :=
    (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
  rw [h3, h4, hfd2, iteratedFDeriv_const_of_ne (by omega : k + 1 ≠ 0)]
  simp

theorem contDiff_uQuad (g : Matrix (Fin 2) (Fin 2) ℂ) : ContDiff ℝ ∞ (uQuad g) := by
  have h : uQuad g = fun w =>
      botNormSqC g * ((w.re - (centerC g).re) ^ 2 + (w.im - (centerC g).im) ^ 2)
        + Complex.normSq g.det / botNormSqC g :=
    funext fun w => uQuad_eq_coords w
  rw [h]
  exact (contDiff_const.mul (((Complex.reCLM.contDiff.sub contDiff_const).pow 2).add
    ((Complex.imCLM.contDiff.sub contDiff_const).pow 2))).add contDiff_const

theorem contDiff_inv_radC (hg : g.det ≠ 0) : ContDiff ℝ ∞ fun w => (radC g w)⁻¹ :=
  (contDiff_radC hg).inv fun z => (radC_pos hg z).ne'

theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1:ℝ)/2) = (Real.sqrt x)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx]
  norm_num

theorem uQuad_le (hg : g.det ≠ 0) (w : ℂ) :
    uQuad g w ≤ (botNormSqC g + Complex.normSq g.det / botNormSqC g)
      * (1 + ‖w - centerC g‖) ^ 2 := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) ≤ Complex.normSq g.det / botNormSqC g :=
    div_nonneg (Complex.normSq_nonneg _) hA.le
  have hd : (0:ℝ) ≤ ‖w - centerC g‖ := norm_nonneg _
  have h1 : Complex.normSq (w - centerC g) = ‖w - centerC g‖ ^ 2 := by
    rw [Complex.sq_norm]
  unfold uQuad
  rw [h1]
  nlinarith [sq_nonneg (‖w - centerC g‖)]

theorem norm_iteratedFDeriv_uQuad_one_le (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ 1 (uQuad g) z‖ ≤ 4 * botNormSqC g * (1 + ‖z - centerC g‖) := by
  refine (norm_iteratedFDeriv_uQuad_one g z).trans ?_
  have hA : (0:ℝ) ≤ botNormSqC g := by
    unfold botNormSqC
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - centerC g)]) (by linarith)

def floorK (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) / 18

theorem floorK_pos (hg : g.det ≠ 0) : 0 < floorK g := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  exact div_pos (lt_min hA hM) (by norm_num)

theorem floorK_mul_lt_uQuad (hg : g.det ≠ 0) (z : ℂ) {v : ℂ} (hv : v ∈ Metric.ball z 1) :
    floorK g * (1 + ‖z - centerC g‖) ^ 2 < uQuad g v := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hmin : (0:ℝ) < min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) := lt_min hA hM
  have hminA : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g) ≤ botNormSqC g :=
    min_le_left _ _
  have hminM : min (botNormSqC g) (Complex.normSq g.det / botNormSqC g)
      ≤ Complex.normSq g.det / botNormSqC g := min_le_right _ _
  have hvz : ‖v - z‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.1 hv
  have hnv : Complex.normSq (v - centerC g) = ‖v - centerC g‖ ^ 2 := by
    rw [Complex.sq_norm]
  have huv : uQuad g v
      = botNormSqC g * ‖v - centerC g‖ ^ 2 + Complex.normSq g.det / botNormSqC g := by
    unfold uQuad
    rw [hnv]
  have hd0 : (0:ℝ) ≤ ‖z - centerC g‖ := norm_nonneg _
  have hvc0 : (0:ℝ) ≤ ‖v - centerC g‖ := norm_nonneg _
  unfold floorK
  rcases le_total (‖z - centerC g‖) 2 with hcase | hcase
  · have h1 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1
      (le_of_lt (div_pos hmin (by norm_num : (0:ℝ) < 18)))
    have h4 : (0:ℝ) ≤ botNormSqC g * ‖v - centerC g‖ ^ 2 :=
      mul_nonneg hA.le (sq_nonneg _)
    rw [huv]
    linarith
  · have hvc : ‖z - centerC g‖ - 1 < ‖v - centerC g‖ := by
      have htri : ‖z - centerC g‖ ≤ ‖z - v‖ + ‖v - centerC g‖ := by
        calc ‖z - centerC g‖ = ‖z - v + (v - centerC g)‖ := by
              rw [show z - v + (v - centerC g) = z - centerC g from by ring]
          _ ≤ ‖z - v‖ + ‖v - centerC g‖ := norm_add_le _ _
      have hzv : ‖z - v‖ < 1 := by rwa [norm_sub_rev]
      linarith
    have hd1 : (0:ℝ) ≤ ‖z - centerC g‖ - 1 := by linarith
    have h1 : 1 + ‖z - centerC g‖ ≤ 3 * (‖z - centerC g‖ - 1) := by linarith
    have h2 : (1 + ‖z - centerC g‖) ^ 2 ≤ 9 * (‖z - centerC g‖ - 1) ^ 2 := by nlinarith
    have h4 : (‖z - centerC g‖ - 1) ^ 2 < ‖v - centerC g‖ ^ 2 := by nlinarith
    have h5 := mul_lt_mul_of_pos_left h4 hA
    rw [huv]
    nlinarith [sq_nonneg (‖z - centerC g‖ - 1), hmin.le, hM.le]

theorem exists_decay_bound_iteratedFDeriv_inv_radC (hg : g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖
        ≤ C / (1 + ‖z - centerC g‖) ^ (n + 1) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hK : (0:ℝ) < floorK g := floorK_pos hg
  have hM0 : (0:ℝ) < Complex.normSq g.det / botNormSqC g :=
    div_pos (Complex.normSq_pos.2 hg) hA
  have hupos : ∀ w : ℂ, (0:ℝ) < uQuad g w := fun w => lt_of_lt_of_le hM0 (uQuad_ge hg w)
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc2 : (0:ℝ) < 4 * botNormSqC g / floorK g + 1 := by
    have h0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
    linarith
  have hsK : (0:ℝ) < (Real.sqrt (floorK g))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hK)
  refine ⟨(n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹,
    mul_pos (mul_pos (mul_pos hfac hfac) (pow_pos hc2 n)) hsK, fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hcz : (0:ℝ) < floorK g * (1 + ‖z - centerC g‖) ^ 2 := mul_pos hK (pow_pos hW0 2)
  have hball : z ∈ Metric.ball z 1 := Metric.mem_ball_self one_pos
  have hmaps : Set.MapsTo (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
      (Metric.ball z 1) (Set.Ioi (1:ℝ)) := fun v hv =>
    Set.mem_Ioi.2 ((one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hv))
  have hrw : (fun w => (radC g w)⁻¹)
      = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
          • ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
             fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) w := by
    funext w
    have hu := hupos w
    have h1 : radC g w = Real.sqrt (uQuad g w) := by
      rw [uQuad_eq_radC_sq hg w, Real.sqrt_sq (radC_pos hg w).le]
    have hL : (Real.sqrt (uQuad g w))⁻¹ = uQuad g w ^ (-(1:ℝ)/2) :=
      (rpow_neg_half_eq_inv_sqrt hu.le).symm
    have hne : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2) ≠ 0 :=
      (Real.rpow_pos_of_pos hcz _).ne'
    have hR : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * (uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) ^ (-(1:ℝ)/2)
        = uQuad g w ^ (-(1:ℝ)/2) := by
      rw [show uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)
          = uQuad g w * (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ from div_eq_mul_inv _ _,
        Real.mul_rpow hu.le (inv_nonneg.2 hcz.le), Real.inv_rpow hcz.le,
        mul_comm (uQuad g w ^ (-(1:ℝ)/2)), ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h1, hL, smul_eq_mul, Function.comp_apply, hR]
  rw [hrw]
  have hũ : ContDiff ℝ ∞ fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (contDiff_uQuad g).div_const _
  have hũz : (1:ℝ) < uQuad g z / (floorK g * (1 + ‖z - centerC g‖) ^ 2) :=
    (one_lt_div hcz).2 (floorK_mul_lt_uQuad hg z hball)
  have hcomp_cd : ContDiffAt ℝ ∞ ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
      fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z :=
    (Real.contDiffAt_rpow_const_of_ne (by linarith : uQuad g z
      / (floorK g * (1 + ‖z - centerC g‖) ^ 2) ≠ 0)).comp z hũ.contDiffAt
  rw [iteratedFDeriv_const_smul_apply' (hcomp_cd.of_le (mod_cast le_top))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hcz _)]
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans one_pos (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi (1:ℝ))
        ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖ ≤ (n ! : ℝ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    calc ‖iteratedDerivWithin i (fun y : ℝ => y ^ (-(1 : ℝ) / 2)) (Set.Ioi 1)
          ((fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) z)‖
        ≤ i ! * (1:ℝ) ^ (-(1 : ℝ) / 2 - i) :=
          norm_iteratedDerivWithin_rpow_neg_half_le one_pos i (hmaps hball)
      _ = (i ! : ℝ) := by rw [Real.one_rpow, mul_one]
      _ ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i
          (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
        ≤ ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ i := by
    intro i hi1 hin
    rw [iteratedFDerivWithin_of_isOpen i Metric.isOpen_ball hball]
    have hsm : (fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2))
        = fun w => (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ • uQuad g w := by
      funext w
      rw [smul_eq_mul, div_eq_inv_mul]
    rw [hsm, iteratedFDeriv_const_smul_apply'
      ((contDiff_uQuad g).contDiffAt.of_le (mod_cast le_top))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcz)]
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hb := norm_iteratedFDeriv_uQuad_one_le g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
            * (4 * botNormSqC g * (1 + ‖z - centerC g‖))
            = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := by
          field_simp
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹
              * (4 * botNormSqC g * (1 + ‖z - centerC g‖)) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * (1 + ‖z - centerC g‖)⁻¹ := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) * (1 + ‖z - centerC g‖)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hW0.le)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 1 := by
              rw [pow_one, ← div_eq_mul_inv]
      · have hb := norm_iteratedFDeriv_uQuad_two g z
        have heq : (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g)
            = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := by
          field_simp
        have hX0 : (0:ℝ) ≤ 4 * botNormSqC g / floorK g := div_nonneg (by linarith) hK.le
        have hX1 : 4 * botNormSqC g / floorK g ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 := by
          nlinarith
        calc (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
            ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2)⁻¹ * (4 * botNormSqC g) :=
              mul_le_mul_of_nonneg_left hb (inv_pos.2 hcz).le
          _ = 4 * botNormSqC g / floorK g * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 := heq
          _ ≤ (4 * botNormSqC g / floorK g + 1) ^ 2 * ((1 + ‖z - centerC g‖)⁻¹) ^ 2 :=
              mul_le_mul_of_nonneg_right hX1 (sq_nonneg _)
          _ = ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ 2 := by
              rw [div_pow, inv_pow, ← div_eq_mul_inv]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, mul_zero]
      exact pow_nonneg (div_nonneg hc2.le hW0.le) i
  have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hgOn hũ.contDiffOn
    (mod_cast le_top) isOpen_Ioi.uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn
    hmaps hball hC hD
  rw [← iteratedFDerivWithin_of_isOpen n Metric.isOpen_ball hball]
  have hczhalf : (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
      = (Real.sqrt (floorK g))⁻¹ * (1 + ‖z - centerC g‖)⁻¹ := by
    have h1 : floorK g * (1 + ‖z - centerC g‖) ^ 2
        = (Real.sqrt (floorK g) * (1 + ‖z - centerC g‖)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
    have hb0 : (0:ℝ) ≤ Real.sqrt (floorK g) * (1 + ‖z - centerC g‖) :=
      mul_nonneg (Real.sqrt_nonneg _) hW0.le
    rw [h1, rpow_neg_half_eq_inv_sqrt (sq_nonneg _), Real.sqrt_sq hb0, mul_inv]
  calc (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ‖iteratedFDerivWithin ℝ n ((fun y : ℝ => y ^ (-(1 : ℝ) / 2)) ∘
            fun w => uQuad g w / (floorK g * (1 + ‖z - centerC g‖) ^ 2)) (Metric.ball z 1) z‖
      ≤ (floorK g * (1 + ‖z - centerC g‖) ^ 2) ^ (-(1:ℝ)/2)
        * ((n ! : ℝ) * n !
          * ((4 * botNormSqC g / floorK g + 1) / (1 + ‖z - centerC g‖)) ^ n) :=
        mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos hcz _).le
    _ = (n ! : ℝ) * n ! * (4 * botNormSqC g / floorK g + 1) ^ n * (Real.sqrt (floorK g))⁻¹
        / (1 + ‖z - centerC g‖) ^ (n + 1) := by
        rw [hczhalf, div_pow, pow_succ]
        have hsne : Real.sqrt (floorK g) ≠ 0 := (Real.sqrt_pos.2 hK).ne'
        field_simp

theorem exists_decay_bound_iteratedFDeriv_radC (hg : g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (radC g) z‖
        ≤ C * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
  obtain ⟨C0, hC0, hB0⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  obtain ⟨C1, hC1, hB1⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 1)
  obtain ⟨C2, hC2, hB2⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 2)
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hM : (0:ℝ) ≤ Complex.normSq g.det / botNormSqC g :=
    div_nonneg (Complex.normSq_nonneg _) hA.le
  have h1p : (0:ℝ) < (botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0 :=
    mul_pos (by linarith) hC0
  have h2p : (0:ℝ) < 4 * botNormSqC g * C1 := mul_pos (by linarith) hC1
  have h3p : (0:ℝ) < 4 * botNormSqC g * C2 := mul_pos (by linarith) hC2
  refine ⟨2 ^ n * ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
      + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2),
    mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) n) (by linarith), fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hrw : radC g = fun w => uQuad g w * (radC g w)⁻¹ := by
    funext w
    rw [uQuad_eq_radC_sq hg w, pow_two, mul_assoc, mul_inv_cancel₀ (radC_pos hg w).ne',
      mul_one]
  rw [hrw]
  refine (norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (contDiff_uQuad g) (contDiff_inv_radC hg) z
    (mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (uQuad g) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w => (radC g w)⁻¹) z‖
        ≤ (n.choose i : ℝ) * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
            + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
            * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge i 3 with h3 | h3
    · interval_cases i
      · have hu0 : ‖iteratedFDeriv ℝ 0 (uQuad g) z‖
            ≤ (botNormSqC g + Complex.normSq g.det / botNormSqC g)
              * (1 + ‖z - centerC g‖) ^ 2 := by
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
            abs_of_pos (lt_of_lt_of_le (div_pos (Complex.normSq_pos.2 hg) hA)
              (uQuad_ge hg z))]
          exact uQuad_le hg z
        calc ‖iteratedFDeriv ℝ 0 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 0) (fun w => (radC g w)⁻¹) z‖
            ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g)
                * (1 + ‖z - centerC g‖) ^ 2) * (C0 / (1 + ‖z - centerC g‖) ^ (n + 1)) := by
              rw [Nat.sub_zero]
              exact mul_le_mul hu0 (hB0 z) (norm_nonneg _)
                (mul_nonneg (by linarith) (sq_nonneg _))
          _ = (botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_two, pow_succ]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h2p, h3p]
      · have hu1 := norm_iteratedFDeriv_uQuad_one_le g z
        have hn1 : 1 ≤ n := hin
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        calc ‖iteratedFDeriv ℝ 1 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
            ≤ (4 * botNormSqC g * (1 + ‖z - centerC g‖))
                * (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) :=
              mul_le_mul hu1 (hB1 z) (norm_nonneg _)
                (mul_nonneg (by linarith) hW0.le)
          _ = 4 * botNormSqC g * C1
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [hsub]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h1p, h3p]
      · have hu2 := norm_iteratedFDeriv_uQuad_two g z
        have hn2 : 2 ≤ n := hin
        have hsub : n - 2 + 1 = n - 1 := by omega
        have hsub2 : n - 1 + 1 = n := by omega
        calc ‖iteratedFDeriv ℝ 2 (uQuad g) z‖
              * ‖iteratedFDeriv ℝ (n - 2) (fun w => (radC g w)⁻¹) z‖
            ≤ (4 * botNormSqC g) * (C2 / (1 + ‖z - centerC g‖) ^ (n - 2 + 1)) :=
              mul_le_mul hu2 (hB2 z) (norm_nonneg _) (by linarith)
          _ = 4 * botNormSqC g * C2
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              rw [hsub, show (1 + ‖z - centerC g‖) ^ n
                  = (1 + ‖z - centerC g‖) ^ (n - 1) * (1 + ‖z - centerC g‖) from by
                rw [← pow_succ, hsub2]]
              field_simp
          _ ≤ ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
                + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
                * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
              gcongr
              linarith [h1p, h2p]
    · rw [norm_iteratedFDeriv_uQuad_ge_three g h3 z, zero_mul]
      positivity
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (uQuad g) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w => (radC g w)⁻¹) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
            + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
            * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) :=
        Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * (((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
          + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
          * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ = 2 ^ n * ((botNormSqC g + Complex.normSq g.det / botNormSqC g) * C0
          + 4 * botNormSqC g * C1 + 4 * botNormSqC g * C2)
          * (1 + ‖z - centerC g‖) / (1 + ‖z - centerC g‖) ^ n := by
        ring

def conjCLM : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap

@[scoped simp] theorem conjCLM_apply (w : ℂ) : conjCLM w = (starRingEnd ℂ) w := rfl

theorem exists_bound_iteratedFDeriv_inv_radC_smul_affine (hg : g.det ≠ 0)
    (c₀ : ℂ) (L : ℂ →L[ℝ] ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹ • (c₀ + L w)) z‖ ≤ C := by
  obtain ⟨C0, hC0, hB0⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  obtain ⟨C1, hC1, hB1⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg (n - 1)
  have hcq0 : (0:ℝ) ≤ ‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖ := by positivity
  have hLC1 : (0:ℝ) ≤ ‖L‖ * C1 := mul_nonneg (norm_nonneg _) hC1.le
  have hcqC0 : (0:ℝ) ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 := mul_nonneg hcq0 hC0.le
  have h2n : (0:ℝ) < 2 ^ n := pow_pos (by norm_num) n
  refine ⟨2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1,
    by nlinarith, fun z => ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
  have hq : ContDiff ℝ ∞ fun w : ℂ => c₀ + L w := contDiff_const.add L.contDiff
  refine (norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (contDiff_inv_radC hg) hq z
    (mod_cast le_top)).trans ?_
  have hq0 : ‖c₀ + L z‖ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖) := by
    have h1 : ‖c₀ + L z‖ ≤ ‖c₀‖ + ‖L‖ * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact L.le_opNorm z
    have h2 : ‖z‖ ≤ ‖z - centerC g‖ + ‖centerC g‖ := by
      calc ‖z‖ = ‖z - centerC g + centerC g‖ := by
            rw [show z - centerC g + centerC g = z from by ring]
        _ ≤ ‖z - centerC g‖ + ‖centerC g‖ := norm_add_le _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg L)
    nlinarith [mul_nonneg (norm_nonneg c₀) (norm_nonneg (z - centerC g)),
      mul_nonneg (mul_nonneg (norm_nonneg L) (norm_nonneg (centerC g)))
        (norm_nonneg (z - centerC g)),
      mul_nonneg (norm_nonneg L) (norm_nonneg (z - centerC g))]
  have hfd : (fderiv ℝ fun w : ℂ => c₀ + L w) = fun _ => L :=
    funext fun w => ((L.hasFDerivAt (x := w)).const_add c₀).fderiv
  have hq1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖ ≤ ‖L‖ := by
    have h1 : ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ 0 (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := 0)).symm
    rw [h1, norm_iteratedFDeriv_zero, hfd]
  have hq2 : ∀ k : ℕ, ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖ = 0 := by
    intro k
    have h1 : ‖iteratedFDeriv ℝ (k + 2) (fun w : ℂ => c₀ + L w) z‖
        = ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ fun w : ℂ => c₀ + L w) z‖ :=
      (norm_iteratedFDeriv_fderiv (n := k + 1)).symm
    rw [h1, hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
          * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
        ≤ (n.choose i : ℝ) * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hbin : (0:ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hbin
    rcases Nat.lt_or_ge (n - i) 2 with h2 | h2
    · have hcase : n - i = 0 ∨ n - i = 1 := by omega
      rcases hcase with h0 | h1
      · have hieq : i = n := by omega
        rw [hieq, Nat.sub_self, norm_iteratedFDeriv_zero]
        calc ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ * ‖c₀ + L z‖
            ≤ (C0 / (1 + ‖z - centerC g‖) ^ (n + 1))
              * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * (1 + ‖z - centerC g‖)) :=
              mul_le_mul (hB0 z) hq0 (norm_nonneg _)
                (div_nonneg hC0.le (pow_nonneg hW0.le _))
          _ = (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 / (1 + ‖z - centerC g‖) ^ n := by
              rw [pow_succ]
              field_simp
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 :=
              div_le_self hcqC0 (one_le_pow₀ hW1)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by linarith
      · have hieq : i = n - 1 := by omega
        have hn1 : 1 ≤ n := by omega
        rw [hieq, show n - (n - 1) = 1 from by omega]
        calc ‖iteratedFDeriv ℝ (n - 1) (fun w => (radC g w)⁻¹) z‖
              * ‖iteratedFDeriv ℝ 1 (fun w : ℂ => c₀ + L w) z‖
            ≤ (C1 / (1 + ‖z - centerC g‖) ^ (n - 1 + 1)) * ‖L‖ :=
              mul_le_mul (hB1 z) hq1 (norm_nonneg _)
                (div_nonneg hC1.le (pow_nonneg hW0.le _))
          _ ≤ C1 * ‖L‖ :=
              mul_le_mul_of_nonneg_right
                (div_le_self hC1.le (one_le_pow₀ hW1)) (norm_nonneg _)
          _ ≤ (‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1 := by
              nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, n - i = k + 2 := ⟨n - i - 2, by omega⟩
      rw [hk, hq2 k, mul_zero]
      nlinarith
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
        * ‖iteratedFDeriv ℝ i (fun w => (radC g w)⁻¹) z‖
        * ‖iteratedFDeriv ℝ (n - i) (fun w : ℂ => c₀ + L w) z‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)
          * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := Finset.sum_le_sum hterm
    _ = (2:ℝ) ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ 2 ^ n * ((‖c₀‖ + ‖L‖ * ‖centerC g‖ + ‖L‖) * C0 + ‖L‖ * C1) + 1 := by linarith

theorem norm_iteratedDerivWithin_rpow_le {c : ℝ} (hc : 0 < c) (r : ℝ) (k : ℕ) {v : ℝ}
    (hv : v ∈ Set.Ioi c) :
    ‖iteratedDerivWithin k (fun y : ℝ => y ^ r) (Set.Ioi c) v‖
      ≤ (∏ j ∈ Finset.range k, (|r| + j)) * v ^ (r - k) := by
  have hvpos : (0:ℝ) < v := hc.trans hv
  rw [iteratedDerivWithin_rpow_const hc r k hv, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hvpos.le _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hvpos.le _)
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
  rw [sub_eq_add_neg]
  calc |r + -(j:ℝ)| = ‖r + -(j:ℝ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖r‖ + ‖-(j:ℝ)‖ := norm_add_le _ _
    _ = |r| + (j:ℝ) := by rw [Real.norm_eq_abs, norm_neg, Real.norm_eq_abs, Nat.abs_cast]

theorem exists_bound_iteratedFDeriv_rpow_neg_radC (hg : g.det ≠ 0) (κ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun w => radC g w ^ (-κ)) z‖ ≤ C * radC g z ^ (-κ) := by
  have hA : (0:ℝ) < botNormSqC g := botNormSqC_pos hg
  have hm : (0:ℝ) < ‖g.det‖ / Real.sqrt (botNormSqC g) :=
    div_pos (norm_pos_iff.2 hg) (Real.sqrt_pos.2 hA)
  have htow : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖iteratedFDeriv ℝ (k + 1) (radC g) z‖ ≤ C := by
    intro k
    obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_radC hg (k + 1)
    refine ⟨C, hC, fun z => (hB z).trans ?_⟩
    have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
    have hW0 : (0:ℝ) < 1 + ‖z - centerC g‖ := by linarith
    have h1 : (1:ℝ) ≤ (1 + ‖z - centerC g‖) ^ k := one_le_pow₀ hW1
    rw [pow_succ, div_le_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hW0.le)
    nlinarith [h2]
  choose CR hCR using htow
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hP : (0:ℝ) < (|(-κ)| + n + 1) ^ n := pow_pos (by positivity) n
  have hMx : (0:ℝ) < max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hDsum : (0:ℝ) ≤ ∑ k ∈ Finset.range n, CR k :=
    Finset.sum_nonneg fun k _ => (hCR k).1.le
  have hD1 : (1:ℝ) ≤ 1 + ∑ k ∈ Finset.range n, CR k := by linarith
  refine ⟨(n ! : ℝ) * (((|(-κ)| + n + 1) ^ n)
      * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n)
      * (1 + ∑ k ∈ Finset.range n, CR k) ^ n,
    mul_pos (mul_pos hfac (mul_pos hP (pow_pos hMx n))) (pow_pos (by linarith) n),
    fun z => ?_⟩
  have hrad := radC_pos hg z
  have hradm := norm_det_div_sqrt_le_radC hg z
  have hm2 : ‖g.det‖ / Real.sqrt (botNormSqC g) / 2 < radC g z := by nlinarith
  have hrange : Set.range (radC g)
      ⊆ Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) := by
    rintro y ⟨w, rfl⟩
    have h1 := norm_det_div_sqrt_le_radC hg w
    have h2 := radC_pos hg w
    exact Set.mem_Ioi.2 (by nlinarith)
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ (-κ))
      (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) :=
    fun y hy => (Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (lt_trans (by linarith) (Set.mem_Ioi.1 hy)))).contDiffWithinAt
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ (-κ))
          (Set.Ioi (‖g.det‖ / Real.sqrt (botNormSqC g) / 2)) (radC g z)‖
        ≤ ((|(-κ)| + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n * radC g z ^ (-κ) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    refine (norm_iteratedDerivWithin_rpow_le (by linarith) (-κ) i
      (Set.mem_Ioi.2 hm2)).trans ?_
    have hsplit : radC g z ^ (-κ - (i:ℝ)) = radC g z ^ (-κ) * (radC g z ^ ((i:ℝ)))⁻¹ := by
      rw [show -κ - (i:ℝ) = -κ + -(i:ℝ) from by ring, Real.rpow_add hrad,
        Real.rpow_neg hrad.le ((i:ℝ))]
    have hpowinv : (radC g z ^ ((i:ℝ)))⁻¹
        ≤ (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n := by
      rw [Real.rpow_natCast]
      have hmh : (0:ℝ) < (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i :=
        pow_pos (by linarith) i
      have h1 : (‖g.det‖ / Real.sqrt (botNormSqC g) / 2) ^ i ≤ radC g z ^ i :=
        pow_le_pow_left₀ (by linarith) (by linarith) i
      have h2 := one_div_le_one_div_of_le hmh h1
      rw [one_div, one_div] at h2
      refine h2.trans ?_
      rw [← inv_pow, inv_div]
      have hb1 : (1:ℝ) ≤ max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) := le_max_left _ _
      have h3 : (2 / (‖g.det‖ / Real.sqrt (botNormSqC g))) ^ i
          ≤ (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ i :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) i
      exact h3.trans (pow_le_pow_right₀ hb1 hi)
    have hprod : (∏ j ∈ Finset.range i, (|(-κ)| + j))
        ≤ (|(-κ)| + n + 1) ^ n := by
      have hstep1 : (∏ j ∈ Finset.range i, (|(-κ)| + j))
          ≤ ∏ _j ∈ Finset.range i, (|(-κ)| + (n:ℝ) + 1) := by
        refine Finset.prod_le_prod (fun j _ => by positivity) (fun j hj => ?_)
        have hjn : (j:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hj) hi)
        linarith
      refine hstep1.trans ?_
      rw [Finset.prod_const, Finset.card_range]
      have hb1 : (1:ℝ) ≤ |(-κ)| + (n:ℝ) + 1 := by
        have h1 := abs_nonneg (-κ)
        have h2 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      exact pow_le_pow_right₀ hb1 hi
    rw [hsplit]
    have hr0 : (0:ℝ) ≤ radC g z ^ (-κ) := Real.rpow_nonneg hrad.le _
    have hi0 : (0:ℝ) ≤ (radC g z ^ ((i:ℝ)))⁻¹ :=
      inv_nonneg.2 (Real.rpow_nonneg hrad.le _)
    calc (∏ j ∈ Finset.range i, (|(-κ)| + j)) * (radC g z ^ (-κ) * (radC g z ^ ((i:ℝ)))⁻¹)
        ≤ ((|(-κ)| + n + 1) ^ n)
          * (radC g z ^ (-κ)
            * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n) :=
          mul_le_mul hprod (mul_le_mul_of_nonneg_left hpowinv hr0)
            (mul_nonneg hr0 hi0) hP.le
      _ = ((|(-κ)| + n + 1) ^ n)
          * (max 1 (2 / (‖g.det‖ / Real.sqrt (botNormSqC g)))) ^ n * radC g z ^ (-κ) := by
          ring
  have hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (radC g) z‖ ≤ (1 + ∑ k ∈ Finset.range n, CR k) ^ i := by
    intro i hi1 hin
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < n := by omega
    have h1 : CR k ≤ 1 + ∑ j ∈ Finset.range n, CR j := by
      have hle := Finset.single_le_sum (f := CR) (fun j _ => (hCR j).1.le)
        (Finset.mem_range.2 hk)
      linarith
    refine ((hCR k).2 z).trans (h1.trans ?_)
    exact le_self_pow₀ hD1 (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) hrange isOpen_Ioi.uniqueDiffOn hgOn
    (contDiff_radC hg) (mod_cast le_top) z hC hD
  have hfun : (fun w => radC g w ^ (-κ)) = (fun y : ℝ => y ^ (-κ)) ∘ radC g := rfl
  rw [hfun]
  refine hcomp.trans (le_of_eq ?_)
  ring

theorem exists_bound_iteratedFDeriv_radC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (radC g) z‖ ≤ C := by
  intro n hn
  obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_radC hg n
  refine ⟨C, hC, fun z => (hB z).trans ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  have h1 : 1 + ‖z - centerC g‖ ≤ (1 + ‖z - centerC g‖) ^ n := le_self_pow₀ hW1 (by omega)
  rw [div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h1 hC.le

theorem exists_bound_iteratedFDeriv_inv_radC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => (radC g w)⁻¹) z‖ ≤ C := by
  intro n
  obtain ⟨C, hC, hB⟩ := exists_decay_bound_iteratedFDeriv_inv_radC hg n
  refine ⟨C, hC, fun z => (hB z).trans ?_⟩
  have hW1 : (1:ℝ) ≤ 1 + ‖z - centerC g‖ := by linarith [norm_nonneg (z - centerC g)]
  exact div_le_self hC.le (one_le_pow₀ hW1)

theorem exists_bound_iteratedFDeriv_kC (hg : g.det ≠ 0) :
    ∀ (n : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by
  intro n
  obtain ⟨C00, h00, hb00⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    ((starRingEnd ℂ) (g 0 1)) ((starRingEnd ℂ) (g 1 1) • conjCLM) n
  obtain ⟨C01, h01, hb01⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (-(starRingEnd ℂ) (g 0 0)) ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) n
  obtain ⟨C10, h10, hb10⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (g 0 0) (g 1 0 • ContinuousLinearMap.id ℝ ℂ) n
  obtain ⟨C11, h11, hb11⟩ := exists_bound_iteratedFDeriv_inv_radC_smul_affine hg
    (g 0 1) (g 1 1 • ContinuousLinearMap.id ℝ ℂ) n
  refine ⟨C00 + C01 + C10 + C11, by linarith, ?_⟩
  intro i j z
  fin_cases i <;> fin_cases j
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 0) z‖ ≤ _
    have heq : (fun w => kC g w 0 0)
        = fun w => (radC g w)⁻¹ • ((starRingEnd ℂ) (g 0 1) + ((starRingEnd ℂ) (g 1 1) • conjCLM) w) := by
      funext w
      show (starRingEnd ℂ) (botQ g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, map_add, map_mul, ContinuousLinearMap.smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb00 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 0 1) z‖ ≤ _
    have heq : (fun w => kC g w 0 1)
        = fun w => (radC g w)⁻¹ • (-(starRingEnd ℂ) (g 0 0) + ((-(starRingEnd ℂ) (g 1 0)) • conjCLM) w) := by
      funext w
      show -(starRingEnd ℂ) (botP g w) / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, map_add, map_mul, ContinuousLinearMap.smul_apply, conjCLM_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb01 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 0) z‖ ≤ _
    have heq : (fun w => kC g w 1 0)
        = fun w => (radC g w)⁻¹ • (g 0 0 + (g 1 0 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botP g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botP, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb10 z).trans (by linarith)
  · show ‖iteratedFDeriv ℝ n (fun w => kC g w 1 1) z‖ ≤ _
    have heq : (fun w => kC g w 1 1)
        = fun w => (radC g w)⁻¹ • (g 0 1 + (g 1 1 • ContinuousLinearMap.id ℝ ℂ) w) := by
      funext w
      show botQ g w / ((radC g w : ℝ) : ℂ) = _
      simp only [botQ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
      ring
    rw [heq]
    exact (hb11 z).trans (by linarith)

end M4aP3C.CplxSmooth
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxSmooth"
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa"

end
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxSmooth"

noncomputable section

open AutomorphicForm.ComplexIwasawa
open scoped ContDiff

theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    (∀ i j : Fin 2, ContDiff ℝ ∞ (fun w => kC g w i j)) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
        ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C :=
  ⟨fun i j => M4aP3C.CplxIwasawa.contDiff_kC_apply hg i j,
    M4aP3C.CplxSmooth.exists_bound_iteratedFDeriv_kC hg⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxIwasawa P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply.M4aP3C.CplxSmooth"

#print axioms solution

end S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply
end P2MW
export P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply (solution)
