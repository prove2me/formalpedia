-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/87a58272-5193-5111-b1f1-8c61d6778b9e

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_GL2Twisted_exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart
import Theorems.Thm_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory TopologicalSpace Topology
open AutomorphicForm AutomorphicForm.GL2Twisted

noncomputable section

namespace P2mOIDiagC

theorem continuousOn_matrixInv :
    ContinuousOn (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) {A | IsUnit A} := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  refine ContinuousOn.smul (f := fun A => (Matrix.det A)⁻¹) (g := Matrix.adjugate) ?_
    (Continuous.matrix_adjugate continuous_id).continuousOn
  exact (Continuous.matrix_det continuous_id).continuousOn.inv₀ fun A hA =>
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero

theorem isEmbedding_glVal : IsEmbedding (Units.val : GL (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.isEmbedding_val_mk' continuousOn_matrixInv fun u => (Matrix.coe_units_inv u).symm

scoped instance t2_GL : T2Space (GL (Fin 2) ℂ) := isEmbedding_glVal.t2Space

scoped instance sc_GL : SecondCountableTopology (GL (Fin 2) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact isEmbedding_glVal.secondCountableTopology

scoped instance lc_GL : LocallyCompactSpace (GL (Fin 2) ℂ) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_glEntry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  isEmbedding_glVal.continuous.matrix_elem i j

theorem continuous_glDet : Continuous fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ).det :=
  isEmbedding_glVal.continuous.matrix_det

def glOf (A : Fin 2 → Fin 2 → ℂ) : GL (Fin 2) ℂ :=
  if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h else 1

theorem det_of_apply (m : Fin 2 → Fin 2 → ℂ) : (Matrix.of m).det = m 0 0 * m 1 1 - m 0 1 * m 1 0 :=
  Matrix.det_fin_two _

theorem glOf_symm_coe (g : GL (Fin 2) ℂ) : glOf (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ)) = g := by
  have hd : (Matrix.of (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  unfold glOf
  rw [dif_pos hd]
  ext i j
  simp

def regSet : Set (Fin 2 → Fin 2 → ℂ) := {A | (Matrix.of A).det ≠ 0}

theorem isOpen_regSet : IsOpen regSet := by
  have h : regSet = {A : Fin 2 → Fin 2 → ℂ | A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0} := by
    ext A
    simp only [regSet, Set.mem_setOf_eq, det_of_apply]
  rw [h]
  exact isOpen_ne_fun (by fun_prop) continuous_const

theorem continuousOn_glOf : ContinuousOn glOf regSet := by
  rw [isEmbedding_glVal.continuousOn_iff]
  have hof : Continuous fun A : Fin 2 → Fin 2 → ℂ => Matrix.of A :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      fun_prop
  have h : Set.EqOn (Units.val ∘ glOf) (fun A => Matrix.of A) regSet := by
    intro A hA
    have hA' : (Matrix.of A).det ≠ 0 := hA
    show ((glOf A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.of A
    unfold glOf
    rw [dif_pos hA']
    rfl
  exact hof.continuousOn.congr h

section Elements

theorem coe_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
        Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
          Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))] :=
  rfl

theorem exp_mul_exp_neg (ξ : ℝ) : Complex.exp (ξ * Complex.I) * Complex.exp (-(ξ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem cos_sq_add_sin_sq' (η : ℝ) : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq η

theorem det_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      Complex.exp (ψ * Complex.I) ^ 2 := by
  rw [coe_unitaryElt, Matrix.det_fin_two_of]
  linear_combination
    Complex.exp (ψ * Complex.I) ^ 2 * (Real.cos η : ℂ) ^ 2 * exp_mul_exp_neg ξ₁ +
      Complex.exp (ψ * Complex.I) ^ 2 * (Real.sin η : ℂ) ^ 2 * exp_mul_exp_neg ξ₂ +
      Complex.exp (ψ * Complex.I) ^ 2 * cos_sq_add_sin_sq' η

theorem norm_exp_mul_I (ξ : ℝ) : ‖Complex.exp (ξ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I ξ

theorem normSq_exp_mul_I (ξ : ℝ) : Complex.normSq (Complex.exp (ξ * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_exp_mul_I, one_pow]

theorem normSq_det_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    Complex.normSq ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [det_unitaryElt, map_pow, normSq_exp_mul_I, one_pow]

theorem norm_det_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ‖((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ = 1 := by
  rw [det_unitaryElt, norm_pow, norm_exp_mul_I, one_pow]

theorem conj_exp_mul_I (ξ : ℝ) : (starRingEnd ℂ) (Complex.exp (ξ * Complex.I)) = Complex.exp (-(ξ * Complex.I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]

theorem conj_exp_neg_mul_I (ξ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(ξ * Complex.I))) = Complex.exp (ξ * Complex.I) := by
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]

open Complex in
theorem conjTranspose_unitaryElt (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose =
      !![exp (-(ψ * I)) * (Real.cos η * exp (-(ξ₁ * I))), exp (-(ψ * I)) * (-(Real.sin η * exp (ξ₂ * I)));
        exp (-(ψ * I)) * (Real.sin η * exp (-(ξ₂ * I))), exp (-(ψ * I)) * (Real.cos η * exp (ξ₁ * I))] := by
  rw [coe_unitaryElt]
  ext i j
  fin_cases i <;> fin_cases j
  · show star (exp (ψ * I) * (Real.cos η * exp (ξ₁ * I))) = _
    rw [star_def, map_mul, map_mul, conj_exp_mul_I, conj_ofReal, conj_exp_mul_I]
    rfl
  · show star (exp (ψ * I) * (-(Real.sin η * exp (-(ξ₂ * I))))) = _
    rw [star_def, map_mul, map_neg, map_mul, conj_exp_mul_I, conj_ofReal, conj_exp_neg_mul_I]
    rfl
  · show star (exp (ψ * I) * (Real.sin η * exp (ξ₂ * I))) = _
    rw [star_def, map_mul, map_mul, conj_exp_mul_I, conj_ofReal, conj_exp_mul_I]
    rfl
  · show star (exp (ψ * I) * (Real.cos η * exp (-(ξ₁ * I)))) = _
    rw [star_def, map_mul, map_mul, conj_exp_mul_I, conj_ofReal, conj_exp_neg_mul_I]
    rfl

theorem unitaryElt_mul_conjTranspose (ψ η ξ₁ ξ₂ : ℝ) :
    ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((unitaryElt ψ η ξ₁ ξ₂ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 := by
  have hψ := exp_mul_exp_neg ψ
  have h1 := exp_mul_exp_neg ξ₁
  have h2 := exp_mul_exp_neg ξ₂
  have h3 := cos_sq_add_sin_sq' η
  rw [conjTranspose_unitaryElt, coe_unitaryElt, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination (Real.cos η : ℂ) ^ 2 * (Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I))) * h1 +
      (Real.sin η : ℂ) ^ 2 * (Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I))) * h2 +
      ((Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2) * hψ + h3
  · ring
  · ring
  · linear_combination (Real.cos η : ℂ) ^ 2 * (Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I))) * h1 +
      (Real.sin η : ℂ) ^ 2 * (Complex.exp (ψ * Complex.I) * Complex.exp (-(ψ * Complex.I))) * h2 +
      ((Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2) * hψ + h3

theorem continuous_unitaryElt : Continuous fun q : ℝ × ℝ × ℝ × ℝ => unitaryElt q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  rw [isEmbedding_glVal.continuous_iff]
  have h : (Units.val ∘ fun q : ℝ × ℝ × ℝ × ℝ => unitaryElt q.1 q.2.1 q.2.2.1 q.2.2.2) =
      fun q : ℝ × ℝ × ℝ × ℝ =>
        !![Complex.exp (q.1 * Complex.I) * (Real.cos q.2.1 * Complex.exp (q.2.2.1 * Complex.I)),
            Complex.exp (q.1 * Complex.I) * (Real.sin q.2.1 * Complex.exp (q.2.2.2 * Complex.I));
          Complex.exp (q.1 * Complex.I) * (-(Real.sin q.2.1 * Complex.exp (-(q.2.2.2 * Complex.I)))),
            Complex.exp (q.1 * Complex.I) * (Real.cos q.2.1 * Complex.exp (-(q.2.2.1 * Complex.I)))] := by
    funext q
    exact coe_unitaryElt _ _ _ _
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem coe_twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) :
    ((twistedSplitElt a₁ a₂ v h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)] :=
  rfl

theorem coe_splitElt (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂) :
    ((twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![(b₁ : ℂ), b₁ * z; 0, (b₂ : ℂ)] := by
  rw [coe_twistedSplitElt, Real.sqrt_sq h.1.le, Real.sqrt_sq h.2.le]

theorem det_splitElt (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂) :
    ((twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det = b₁ * b₂ := by
  rw [coe_splitElt b₁ b₂ z h, Matrix.det_fin_two_of]
  ring

end Elements

section Coordinates

def W₀ : Set ℂ := {α | 0 < α.re ∧ α.re < Real.pi ∧ 0 < α.im ∧ α.im < Real.pi / 2}

def W₁ : Set ℂ := {α | 0 < α.re ∧ α.re < 2 * Real.pi ∧ 0 < α.im ∧ α.im < 2 * Real.pi}

def Qpos : Set ℂ := {β | 0 < β.re ∧ 0 < β.im}

theorem isOpen_W₀ : IsOpen W₀ := by
  have : W₀ = Complex.re ⁻¹' Set.Ioo 0 Real.pi ∩ Complex.im ⁻¹' Set.Ioo 0 (Real.pi / 2) := by
    ext α; simp [W₀, and_assoc]
  rw [this]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem isOpen_W₁ : IsOpen W₁ := by
  have : W₁ = Complex.re ⁻¹' Set.Ioo 0 (2 * Real.pi) ∩ Complex.im ⁻¹' Set.Ioo 0 (2 * Real.pi) := by
    ext α; simp [W₁, and_assoc]
  rw [this]
  exact (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem isOpen_Qpos : IsOpen Qpos := by
  have : Qpos = Complex.re ⁻¹' Set.Ioi 0 ∩ Complex.im ⁻¹' Set.Ioi 0 := by
    ext α; simp [Qpos]
  rw [this]
  exact (isOpen_Ioi.preimage Complex.continuous_re).inter (isOpen_Ioi.preimage Complex.continuous_im)

end Coordinates

section Invariants

def Qq (x : GL (Fin 2) ℂ) : ℝ :=
  Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) + Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)

def Pq (x : GL (Fin 2) ℂ) : ℝ :=
  Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
    (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1))

def Dq (x : GL (Fin 2) ℂ) : ℝ := Complex.normSq (x : Matrix (Fin 2) (Fin 2) ℂ).det

theorem continuous_Qq : Continuous Qq := by
  unfold Qq
  exact (Complex.continuous_normSq.comp (continuous_glEntry 1 0)).add
    (Complex.continuous_normSq.comp (continuous_glEntry 1 1))

theorem continuous_Pq : Continuous Pq := by
  unfold Pq
  refine Complex.continuous_normSq.comp ?_
  exact ((continuous_glEntry 0 0).mul (Complex.continuous_conj.comp (continuous_glEntry 1 0))).add
    ((continuous_glEntry 0 1).mul (Complex.continuous_conj.comp (continuous_glEntry 1 1)))

theorem continuous_Dq : Continuous Dq := by
  unfold Dq
  exact Complex.continuous_normSq.comp continuous_glDet

theorem Dq_pos (x : GL (Fin 2) ℂ) : 0 < Dq x :=
  Complex.normSq_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero x)

theorem Qq_pos (x : GL (Fin 2) ℂ) : 0 < Qq x := by
  unfold Qq
  by_contra h
  have h0 : Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 0 := by
    have := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    have := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
    linarith
  have h1 : Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1) = 0 := by
    have := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    have := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
    linarith
  rw [Complex.normSq_eq_zero] at h0 h1
  apply Matrix.GeneralLinearGroup.det_ne_zero x
  rw [Matrix.det_fin_two, h0, h1, mul_zero, mul_zero, sub_zero]

theorem Qq_ne (x : GL (Fin 2) ℂ) : Qq x ≠ 0 := (Qq_pos x).ne'
theorem Dq_ne (x : GL (Fin 2) ℂ) : Dq x ≠ 0 := (Dq_pos x).ne'
theorem Pq_nonneg (x : GL (Fin 2) ℂ) : 0 ≤ Pq x := Complex.normSq_nonneg _

def gram (x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (x : Matrix (Fin 2) (Fin 2) ℂ) * (x : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose

theorem gram_apply (x : GL (Fin 2) ℂ) (i j : Fin 2) :
    gram x i j = (x : Matrix (Fin 2) (Fin 2) ℂ) i 0 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) j 0) +
      (x : Matrix (Fin 2) (Fin 2) ℂ) i 1 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) j 1) := by
  simp only [gram, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.star_def]

theorem gram_one_one (x : GL (Fin 2) ℂ) : gram x 1 1 = (Qq x : ℂ) := by
  rw [gram_apply, Qq, Complex.ofReal_add, Complex.mul_conj, Complex.mul_conj]

theorem Pq_eq (x : GL (Fin 2) ℂ) : Pq x = Complex.normSq (gram x 0 1) := by
  rw [gram_apply, Pq]

theorem gram_mul_unitaryElt (x : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) :
    gram (x * unitaryElt ψ η ξ₁ ξ₂) = gram x := by
  unfold gram
  rw [Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (x : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose, unitaryElt_mul_conjTranspose,
    Matrix.one_mul]

theorem Qq_mul_unitaryElt (x : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) : Qq (x * unitaryElt ψ η ξ₁ ξ₂) = Qq x := by
  have h := gram_mul_unitaryElt x ψ η ξ₁ ξ₂
  have h1 : (Qq (x * unitaryElt ψ η ξ₁ ξ₂) : ℂ) = (Qq x : ℂ) := by
    rw [← gram_one_one, ← gram_one_one, h]
  exact_mod_cast h1

theorem Pq_mul_unitaryElt (x : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) : Pq (x * unitaryElt ψ η ξ₁ ξ₂) = Pq x := by
  rw [Pq_eq, Pq_eq, gram_mul_unitaryElt]

theorem Dq_mul_unitaryElt (x : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) : Dq (x * unitaryElt ψ η ξ₁ ξ₂) = Dq x := by
  unfold Dq
  rw [Units.val_mul, Matrix.det_mul, map_mul, normSq_det_unitaryElt, mul_one]

theorem lagrange (x : GL (Fin 2) ℂ) :
    (Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0) + Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1)) *
        Qq x - Pq x = Dq x := by
  unfold Qq Pq Dq
  rw [Matrix.det_fin_two]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem normSq_entry_le_zero_row (x : GL (Fin 2) ℂ) (j : Fin 2) :
    Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 j) ≤ (Dq x + Pq x) / Qq x := by
  rw [le_div_iff₀ (Qq_pos x), ← lagrange x]
  have h0 := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  have h1 := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
  have hQ := (Qq_pos x).le
  fin_cases j <;> simp <;> nlinarith

theorem normSq_entry_le_one_row (x : GL (Fin 2) ℂ) (j : Fin 2) :
    Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 j) ≤ Qq x := by
  have h0 := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
  have h1 := Complex.normSq_nonneg ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)
  unfold Qq
  fin_cases j <;> simp <;> linarith

theorem diag_mul_apply (t x : GL (Fin 2) ℂ) (h01 : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) (i j : Fin 2) :
    ((t * x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      (t : Matrix (Fin 2) (Fin 2) ℂ) i i * (x : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i
  · simp [h01]
  · simp [h10]

theorem det_diag (t : GL (Fin 2) ℂ) (h01 : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) :
    (t : Matrix (Fin 2) (Fin 2) ℂ).det = (t : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (t : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero]

theorem Qq_diag_mul (t x : GL (Fin 2) ℂ) (h01 : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) :
    Qq (t * x) = Complex.normSq ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * Qq x := by
  unfold Qq
  rw [diag_mul_apply t x h01 h10, diag_mul_apply t x h01 h10, map_mul, map_mul]
  ring

theorem Pq_diag_mul (t x : GL (Fin 2) ℂ) (h01 : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) :
    Pq (t * x) = Complex.normSq ((t : Matrix (Fin 2) (Fin 2) ℂ) 0 0) *
      Complex.normSq ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * Pq x := by
  unfold Pq
  rw [diag_mul_apply t x h01 h10, diag_mul_apply t x h01 h10, diag_mul_apply t x h01 h10,
    diag_mul_apply t x h01 h10]
  have : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
        (starRingEnd ℂ) ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
      (t : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 *
        (starRingEnd ℂ) ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (x : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
      ((t : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (starRingEnd ℂ) ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) *
        ((x : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          (x : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (starRingEnd ℂ) ((x : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) := by
    simp only [map_mul]; ring
  rw [this, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj]

theorem Dq_diag_mul (t x : GL (Fin 2) ℂ) (h01 : (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) :
    Dq (t * x) = Complex.normSq ((t : Matrix (Fin 2) (Fin 2) ℂ) 0 0) *
      Complex.normSq ((t : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * Dq x := by
  unfold Dq
  rw [Units.val_mul, Matrix.det_mul, det_diag t h01 h10, map_mul, map_mul]

theorem sq_Pq_le (a₁ a₂ : ℂ) (γ x : GL (Fin 2) ℂ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) :
    Complex.normSq (a₁ - a₂) * Pq x ≤
      (‖((x⁻¹ * γ * x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ +
        ‖((x⁻¹ * γ * x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖) ^ 2 * Dq x := by
  set y : GL (Fin 2) ℂ := x⁻¹ * γ * x with hy
  set X : Matrix (Fin 2) (Fin 2) ℂ := (x : Matrix (Fin 2) (Fin 2) ℂ) with hX
  set Y : Matrix (Fin 2) (Fin 2) ℂ := (y : Matrix (Fin 2) (Fin 2) ℂ) with hY
  have hxy : X * Y = (γ : Matrix (Fin 2) (Fin 2) ℂ) * X := by
    rw [hX, hY, ← Units.val_mul, ← Units.val_mul, hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hγ] at hxy
  have e00 := congr_fun (congr_fun hxy 0) 0
  have e01 := congr_fun (congr_fun hxy 0) 1
  have e10 := congr_fun (congr_fun hxy 1) 0
  have e11 := congr_fun (congr_fun hxy 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, add_zero, zero_add] at e00 e01 e10 e11
  have hdet : X.det = X 0 0 * X 1 1 - X 0 1 * X 1 0 := Matrix.det_fin_two _
  have k10 : X.det * Y 1 0 = (a₂ - a₁) * (X 0 0 * X 1 0) := by
    rw [hdet]; linear_combination X 0 0 * e10 - X 1 0 * e00
  have k01 : X.det * Y 0 1 = (a₁ - a₂) * (X 0 1 * X 1 1) := by
    rw [hdet]; linear_combination X 1 1 * e01 - X 0 1 * e11

  have n10 : ‖a₁ - a₂‖ * (‖X 0 0‖ * ‖X 1 0‖) = ‖X.det‖ * ‖Y 1 0‖ := by
    have := congrArg (fun z : ℂ => ‖z‖) k10
    simp only [norm_mul] at this
    rw [this, norm_sub_rev]
  have n01 : ‖a₁ - a₂‖ * (‖X 0 1‖ * ‖X 1 1‖) = ‖X.det‖ * ‖Y 0 1‖ := by
    have := congrArg (fun z : ℂ => ‖z‖) k01
    simp only [norm_mul] at this
    rw [this]
  have hP : Pq x = ‖X 0 0 * (starRingEnd ℂ) (X 1 0) + X 0 1 * (starRingEnd ℂ) (X 1 1)‖ ^ 2 := by
    rw [Pq, Complex.normSq_eq_norm_sq]
  have hD : Dq x = ‖X.det‖ ^ 2 := by rw [Dq, Complex.normSq_eq_norm_sq]
  have htri : ‖a₁ - a₂‖ * ‖X 0 0 * (starRingEnd ℂ) (X 1 0) + X 0 1 * (starRingEnd ℂ) (X 1 1)‖ ≤
      ‖X.det‖ * (‖Y 0 1‖ + ‖Y 1 0‖) := by
    calc ‖a₁ - a₂‖ * ‖X 0 0 * (starRingEnd ℂ) (X 1 0) + X 0 1 * (starRingEnd ℂ) (X 1 1)‖
        ≤ ‖a₁ - a₂‖ * (‖X 0 0 * (starRingEnd ℂ) (X 1 0)‖ + ‖X 0 1 * (starRingEnd ℂ) (X 1 1)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖X.det‖ * (‖Y 0 1‖ + ‖Y 1 0‖) := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, mul_add, n10, n01]; ring
  rw [Complex.normSq_eq_norm_sq, hP, hD, ← mul_pow, ← mul_pow, mul_comm (‖Y 0 1‖ + ‖Y 1 0‖)]
  exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) htri 2

theorem isCompact_box (M : ℝ) :
    IsCompact {x : GL (Fin 2) ℂ | (∀ i j, Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ M) ∧ 1 ≤ Dq x} := by
  set K₀ : Set (Fin 2 → Fin 2 → ℂ) := {A | (∀ i j, Complex.normSq (A i j) ≤ M) ∧ 1 ≤ Complex.normSq (Matrix.of A).det}
    with hK₀
  have hK₀c : IsCompact K₀ := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have h1 : IsClosed {A : Fin 2 → Fin 2 → ℂ | ∀ i j, Complex.normSq (A i j) ≤ M} := by
        have : {A : Fin 2 → Fin 2 → ℂ | ∀ i j, Complex.normSq (A i j) ≤ M} =
            ⋂ i, ⋂ j, {A | Complex.normSq (A i j) ≤ M} := by
          ext A; simp
        rw [this]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le (Complex.continuous_normSq.comp (by fun_prop)) continuous_const
      have h2 : IsClosed {A : Fin 2 → Fin 2 → ℂ | 1 ≤ Complex.normSq (Matrix.of A).det} := by
        refine isClosed_le continuous_const (Complex.continuous_normSq.comp ?_)
        simp only [det_of_apply]
        fun_prop
      rw [hK₀, Set.setOf_and]
      exact h1.inter h2
    · rw [Metric.isBounded_iff_subset_closedBall (0 : Fin 2 → Fin 2 → ℂ)]
      refine ⟨Real.sqrt (max M 0), fun A hA => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro j
      have h := hA.1 i j
      rw [Complex.normSq_eq_norm_sq] at h
      calc ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (max M 0) := Real.sqrt_le_sqrt (h.trans (le_max_left _ _))
  have hsub : K₀ ⊆ regSet := fun A hA h0 => by
    have h := hA.2
    rw [show (Matrix.of A).det = 0 from h0, map_zero] at h
    exact absurd h (by norm_num)
  have himg : {x : GL (Fin 2) ℂ | (∀ i j, Complex.normSq ((x : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ M) ∧ 1 ≤ Dq x} =
      glOf '' K₀ := by
    ext x
    constructor
    · intro hx
      refine ⟨Matrix.of.symm (x : Matrix (Fin 2) (Fin 2) ℂ), ⟨fun i j => hx.1 i j, ?_⟩, glOf_symm_coe x⟩
      rw [Equiv.apply_symm_apply]
      exact hx.2
    · rintro ⟨A, hA, rfl⟩
      have hd : (Matrix.of A).det ≠ 0 := hsub hA
      have hval : ((glOf A : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.of A := by
        unfold glOf; rw [dif_pos hd]; rfl
      refine ⟨fun i j => ?_, ?_⟩
      · rw [hval]; exact hA.1 i j
      · unfold Dq; rw [hval]; exact hA.2
  rw [himg]
  exact hK₀c.image_of_continuousOn (continuousOn_glOf.mono hsub)

end Invariants

section Centralizer

theorem offdiag_of_mem_centralizer {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂) {t : GL (Fin 2) ℂ}
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) :
    (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ht
  have h := congrArg (Units.val) ht
  rw [Units.val_mul, Units.val_mul, hγ] at h
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have hsub : a₁ - a₂ ≠ 0 := sub_ne_zero.2 hne
  constructor
  · have : (a₂ - a₁) * (t : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by linear_combination e01
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1).symm hne
    · exact h1
  · have : (a₁ - a₂) * (t : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by linear_combination e10
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 hsub
    · exact h1

def diagGL (α β : ℂ) (h : α * β ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, 0; 0, β] (by rw [Matrix.det_fin_two_of]; simpa using h)

theorem coe_diagGL (α β : ℂ) (h : α * β ≠ 0) :
    ((diagGL α β h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![α, 0; 0, β] := rfl

theorem diagGL_mem_centralizer {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (α β : ℂ) (h : α * β ≠ 0) :
    diagGL α β h ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hγ, coe_diagGL, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

def diagT {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (α β : ℂ) (h : α * β ≠ 0) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)) :=
  ⟨diagGL α β h, diagGL_mem_centralizer hγ α β h⟩

theorem coe_diagT {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (α β : ℂ) (h : α * β ≠ 0) :
    ((diagT hγ α β h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![α, 0; 0, β] := rfl

end Centralizer

section Probe

def ρ₀ (s : ℝ) : ℝ := max 0 (min (s - 1) (2 - s))

theorem continuous_ρ₀ : Continuous ρ₀ := by
  unfold ρ₀; fun_prop

theorem ρ₀_nonneg (s : ℝ) : 0 ≤ ρ₀ s := le_max_left _ _

theorem ρ₀_ne_zero_imp {s : ℝ} (h : ρ₀ s ≠ 0) : 1 < s ∧ s < 2 := by
  unfold ρ₀ at h
  by_contra hc
  apply h
  apply max_eq_left
  rw [not_and_or, not_lt, not_lt] at hc
  rcases hc with hc | hc
  · exact min_le_of_left_le (by linarith)
  · exact min_le_of_right_le (by linarith)

theorem ρ₀_three_halves : ρ₀ (3 / 2) = 1 / 2 := by
  unfold ρ₀; norm_num

def χc (R s : ℝ) : ℝ := max 0 (min 1 (R + 1 - s))

theorem continuous_χc (R : ℝ) : Continuous (χc R) := by
  unfold χc; fun_prop

theorem χc_nonneg (R s : ℝ) : 0 ≤ χc R s := le_max_left _ _

theorem χc_le_one (R s : ℝ) : χc R s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem χc_eq_one {R s : ℝ} (h : s ≤ R) : χc R s = 1 := by
  unfold χc
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem χc_ne_zero_imp {R s : ℝ} (h : χc R s ≠ 0) : s < R + 1 := by
  unfold χc at h
  by_contra hc
  apply h
  rw [not_lt] at hc
  exact max_eq_left (min_le_of_right_le (by linarith))

def g₁ (γ : GL (Fin 2) ℂ) (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : ℝ :=
  ρ₀ (Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) *
    ρ₀ (Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1))

theorem continuous_g₁ (γ : GL (Fin 2) ℂ) : Continuous (g₁ γ) := by
  unfold g₁
  exact ((continuous_ρ₀.comp (Complex.continuous_normSq.comp ((continuous_glEntry 0 0).comp
    continuous_subtype_val))).mul (continuous_ρ₀.comp (Complex.continuous_normSq.comp
    ((continuous_glEntry 1 1).comp continuous_subtype_val))))

theorem g₁_nonneg (γ : GL (Fin 2) ℂ) (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : 0 ≤ g₁ γ t :=
  mul_nonneg (ρ₀_nonneg _) (ρ₀_nonneg _)

theorem hasCompactSupport_g₁ {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂) : HasCompactSupport (g₁ γ) := by

  have hTc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : Set (GL (Fin 2) ℂ)) := by
    show IsClosed (({γ} : Set (GL (Fin 2) ℂ)).centralizer)
    exact Set.isClosed_centralizer _
  have hemb : IsClosedEmbedding (Subtype.val : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)) → GL (Fin 2) ℂ) :=
    hTc.isClosedEmbedding_subtypeVal
  refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_box 2)) fun t ht => ?_
  by_contra hg
  apply ht
  have h1 : ρ₀ (Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0)) ≠ 0 := fun h => hg (by
    unfold g₁; rw [h, zero_mul])
  have h2 : ρ₀ (Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) ≠ 0 := fun h => hg (by
    unfold g₁; rw [h, mul_zero])
  obtain ⟨l1, u1⟩ := ρ₀_ne_zero_imp h1
  obtain ⟨l2, u2⟩ := ρ₀_ne_zero_imp h2
  obtain ⟨h01, h10⟩ := offdiag_of_mem_centralizer hγ hne t.2
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j
    · exact u1.le
    · simp [h01]
    · simp [h10]
    · exact u2.le
  · show 1 ≤ Dq (t : GL (Fin 2) ℂ)
    unfold Dq
    rw [det_diag _ h01 h10, map_mul]
    nlinarith

def Cτ (γ : GL (Fin 2) ℂ) (τ : Measure[centralizerBorel ℂ γ] (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)))) : ℝ :=
  ∫ t, g₁ γ t ∂τ

theorem Cτ_pos {a₁ a₂ : ℂ} {γ : GL (Fin 2) ℂ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂)
    (τ : Measure[centralizerBorel ℂ γ] (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) : 0 < Cτ γ τ := by
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := centralizerBorel ℂ γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := ⟨rfl⟩
  haveI := hτ
  have h32 : (Real.sqrt (3 / 2) : ℂ) * (Real.sqrt (3 / 2) : ℂ) ≠ 0 := by
    have : (Real.sqrt (3 / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3 / 2)).ne'
    exact mul_ne_zero this this
  have hns : Complex.normSq (Real.sqrt (3 / 2) : ℂ) = 3 / 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (continuous_g₁ γ)
    (hasCompactSupport_g₁ hγ hne) (g₁_nonneg γ) (x := diagT hγ _ _ h32) ?_
  unfold g₁
  rw [coe_diagT]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, hns, ρ₀_three_halves]
  norm_num

variable (γ : GL (Fin 2) ℂ) (τ : Measure[centralizerBorel ℂ γ] (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))))

def probe (R : ℝ) (x : GL (Fin 2) ℂ) : ℝ :=
  ρ₀ (Dq x / Qq x) * ρ₀ (Qq x) * χc R (Pq x / Dq x) / Cτ γ τ

theorem continuous_probe (R : ℝ) : Continuous (probe γ τ R) := by
  unfold probe
  refine Continuous.div_const ?_ _
  refine ((continuous_ρ₀.comp ?_).mul (continuous_ρ₀.comp continuous_Qq)).mul ((continuous_χc R).comp ?_)
  · exact continuous_Dq.div continuous_Qq fun x => Qq_ne x
  · exact continuous_Pq.div continuous_Dq fun x => Dq_ne x

theorem probe_nonneg {a₁ a₂ : ℂ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂)
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) (R : ℝ)
    (x : GL (Fin 2) ℂ) : 0 ≤ probe γ τ R x :=
  div_nonneg (mul_nonneg (mul_nonneg (ρ₀_nonneg _) (ρ₀_nonneg _)) (χc_nonneg _ _))
    (Cτ_pos hγ hne τ hτ).le

theorem hasCompactSupport_probe (R : ℝ) (hR : 0 ≤ R) : HasCompactSupport (probe γ τ R) := by
  refine HasCompactSupport.intro (isCompact_box (8 + 4 * R)) fun x hx => ?_
  by_contra hp
  apply hx
  unfold probe at hp
  have hC : ρ₀ (Dq x / Qq x) * ρ₀ (Qq x) * χc R (Pq x / Dq x) ≠ 0 := fun h => hp (by rw [h, zero_div])
  have h1 : ρ₀ (Dq x / Qq x) ≠ 0 := fun h => hC (by rw [h, zero_mul, zero_mul])
  have h2 : ρ₀ (Qq x) ≠ 0 := fun h => hC (by rw [h, mul_zero, zero_mul])
  have h3 : χc R (Pq x / Dq x) ≠ 0 := fun h => hC (by rw [h, mul_zero])
  obtain ⟨l1, u1⟩ := ρ₀_ne_zero_imp h1
  obtain ⟨l2, u2⟩ := ρ₀_ne_zero_imp h2
  have u3 := χc_ne_zero_imp h3
  have hQ := Qq_pos x
  have hD := Dq_pos x
  rw [lt_div_iff₀ hQ] at l1
  rw [div_lt_iff₀ hQ] at u1
  rw [div_lt_iff₀ hD] at u3
  have hD4 : Dq x < 4 := by nlinarith
  have hP : Pq x < 4 * (R + 1) := by nlinarith [Pq_nonneg x]
  refine ⟨fun i j => ?_, by nlinarith⟩
  fin_cases i
  · refine (normSq_entry_le_zero_row x j).trans ?_
    rw [div_le_iff₀ hQ]
    nlinarith [Pq_nonneg x]
  · exact (normSq_entry_le_one_row x j).trans (by linarith)

theorem probe_diag_mul {a₁ a₂ : ℂ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂)
    (R : ℝ) (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)))
    (x : GL (Fin 2) ℂ) :
    probe γ τ R ((t : GL (Fin 2) ℂ) * x) =
      g₁ γ (t * diagT hγ (Real.sqrt (Dq x / Qq x)) (Real.sqrt (Qq x))
        (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (div_pos (Dq_pos x) (Qq_pos x))).ne')
          (by exact_mod_cast (Real.sqrt_pos.2 (Qq_pos x)).ne'))) *
        (χc R (Pq x / Dq x) / Cτ γ τ) := by
  obtain ⟨h01, h10⟩ := offdiag_of_mem_centralizer hγ hne t.2
  have hQ := Qq_pos x
  have hD := Dq_pos x
  have ht0 : Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ≠ 0 ∧
      Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1) ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero (t : GL (Fin 2) ℂ)
    rw [det_diag _ h01 h10] at hd
    exact ⟨Complex.normSq_pos.2 (left_ne_zero_of_mul hd) |>.ne', Complex.normSq_pos.2 (right_ne_zero_of_mul hd) |>.ne'⟩
  obtain ⟨ht00, ht11⟩ := ht0
  have e1 : Dq ((t : GL (Fin 2) ℂ) * x) / Qq ((t : GL (Fin 2) ℂ) * x) =
      Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * (Dq x / Qq x) := by
    rw [Dq_diag_mul _ _ h01 h10, Qq_diag_mul _ _ h01 h10]
    field_simp
  have e2 : Qq ((t : GL (Fin 2) ℂ) * x) = Complex.normSq (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * Qq x :=
    Qq_diag_mul _ _ h01 h10
  have e3 : Pq ((t : GL (Fin 2) ℂ) * x) / Dq ((t : GL (Fin 2) ℂ) * x) = Pq x / Dq x := by
    rw [Dq_diag_mul _ _ h01 h10, Pq_diag_mul _ _ h01 h10]
    field_simp

  have hs : ∀ (α β : ℂ) (h : α * β ≠ 0),
      (((t * diagT hγ α β h : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * α ∧
      (((t * diagT hγ α β h : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) : GL (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1) * β := by
    intro α β h
    rw [Subgroup.coe_mul, Units.val_mul, coe_diagT]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10]
  unfold probe g₁
  obtain ⟨hs0, hs1⟩ := hs (Real.sqrt (Dq x / Qq x)) (Real.sqrt (Qq x))
    (mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 (div_pos (Dq_pos x) (Qq_pos x))).ne')
      (by exact_mod_cast (Real.sqrt_pos.2 (Qq_pos x)).ne'))
  rw [e1, e2, e3, hs0, hs1, map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Real.mul_self_sqrt (div_pos hD hQ).le, Real.mul_self_sqrt hQ.le]
  ring

theorem integral_probe_translate {a₁ a₂ : ℂ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂])
    (hne : a₁ ≠ a₂) (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ)
    (R : ℝ) (x : GL (Fin 2) ℂ) :
    ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)), probe γ τ R ((t : GL (Fin 2) ℂ) * x) ∂τ =
      χc R (Pq x / Dq x) := by
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := centralizerBorel ℂ γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := ⟨rfl⟩
  haveI := hτ
  have hcomm : ∀ s t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ)), s * t = t * s := by
    intro s t
    obtain ⟨s01, s10⟩ := offdiag_of_mem_centralizer hγ hne s.2
    obtain ⟨t01, t10⟩ := offdiag_of_mem_centralizer hγ hne t.2
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    fin_cases i <;> fin_cases j
    · rw [diag_mul_apply _ _ s01 s10, diag_mul_apply _ _ t01 t10]; ring
    · rw [diag_mul_apply _ _ s01 s10, diag_mul_apply _ _ t01 t10]; simp [s01, t01]
    · rw [diag_mul_apply _ _ s01 s10, diag_mul_apply _ _ t01 t10]; simp [s10, t10]
    · rw [diag_mul_apply _ _ s01 s10, diag_mul_apply _ _ t01 t10]; ring
  letI : CommGroup (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := { mul_comm := hcomm }
  haveI : τ.IsMulRightInvariant := IsMulLeftInvariant.isMulRightInvariant
  simp_rw [probe_diag_mul γ τ hγ hne R]
  rw [integral_mul_const]
  rw [integral_mul_right_eq_self (fun t => g₁ γ t)]
  show Cτ γ τ * (χc R (Pq x / Dq x) / Cτ γ τ) = χc R (Pq x / Dq x)
  have hC := (Cτ_pos hγ hne τ hτ).ne'
  field_simp

end Probe

section Conj

theorem det_upper (a₁ a₂ v : ℂ) : Matrix.det !![a₁, v; 0, a₂] = a₁ * a₂ := by
  rw [Matrix.det_fin_two_of]; ring

def U (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (v : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, v; 0, a₂] (by rw [det_upper]; exact ha)

theorem coe_U (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (v : ℂ) :
    ((U a₁ a₂ ha v : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, v; 0, a₂] := rfl

theorem continuous_U (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) : Continuous (U a₁ a₂ ha) := by
  rw [isEmbedding_glVal.continuous_iff]
  have h : Units.val ∘ U a₁ a₂ ha = fun v => !![a₁, v; 0, a₂] := by
    funext v; exact coe_U a₁ a₂ ha v
  rw [h]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem splitElt_conj (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (γ : GL (Fin 2) ℂ)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂)
    (k : GL (Fin 2) ℂ) :
    (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ * k)⁻¹ * γ *
        (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ * k) =
      k⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * k := by
  set S : GL (Fin 2) ℂ := twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ with hS
  have hSU : γ * S = S * U a₁ a₂ ha ((a₁ - a₂) * z) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hγ, hS, coe_splitElt b₁ b₂ z h, coe_U, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj, and_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring
  have h1 : S⁻¹ * γ * S = U a₁ a₂ ha ((a₁ - a₂) * z) := by
    rw [mul_assoc, hSU, inv_mul_cancel_left]
  calc (S * k)⁻¹ * γ * (S * k) = k⁻¹ * (S⁻¹ * γ * S) * k := by simp only [mul_inv_rev, mul_assoc]
    _ = k⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * k := by rw [h1]

theorem Qq_splitElt (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂) :
    Qq (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩) = b₂ ^ 2 := by
  unfold Qq
  rw [coe_splitElt b₁ b₂ z h]
  simp [Complex.normSq_ofReal]
  ring

theorem Dq_splitElt (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂) :
    Dq (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩) = (b₁ * b₂) ^ 2 := by
  unfold Dq
  rw [det_splitElt b₁ b₂ z h, show ((b₁ : ℂ) * b₂) = ((b₁ * b₂ : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
  ring

theorem Pq_splitElt (b₁ b₂ : ℝ) (z : ℂ) (h : 0 < b₁ ∧ 0 < b₂) :
    Pq (twistedSplitElt (b₁ ^ 2) (b₂ ^ 2) (b₁ * z) ⟨pow_pos h.1 2, pow_pos h.2 2⟩) = (b₁ * b₂) ^ 2 * Complex.normSq z := by
  unfold Pq
  rw [coe_splitElt b₁ b₂ z h]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, map_zero, mul_zero, zero_add, Complex.conj_ofReal]
  rw [map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring

end Conj

section Assembly

variable (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0) (γ : GL (Fin 2) ℂ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂])

def ka (a : ℂ × ℂ) : GL (Fin 2) ℂ := unitaryElt a.1.re a.1.im a.2.re a.2.im

def kk (r : (ℝ × ℝ) × (ℝ × ℝ)) : GL (Fin 2) ℂ := unitaryElt r.1.1 r.1.2 r.2.1 r.2.2

theorem continuous_kk : Continuous kk := by
  have h : kk = (fun q : ℝ × ℝ × ℝ × ℝ => unitaryElt q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
      (fun r : (ℝ × ℝ) × (ℝ × ℝ) => (r.1.1, r.1.2, r.2.1, r.2.2)) := rfl
  rw [h]
  exact continuous_unitaryElt.comp (by fun_prop)

theorem continuous_ka : Continuous ka := by
  have h : ka = (fun q : ℝ × ℝ × ℝ × ℝ => unitaryElt q.1 q.2.1 q.2.2.1 q.2.2.2) ∘
      (fun a : ℂ × ℂ => (a.1.re, a.1.im, a.2.re, a.2.im)) := rfl
  rw [h]
  exact continuous_unitaryElt.comp (by fun_prop)

def Hf (f : GL (Fin 2) ℂ → ℂ) (q : ((ℝ × ℝ) × (ℝ × ℝ)) × ℂ) : ℂ :=
  ((Real.sin q.1.1.2 : ℂ) * (Real.cos q.1.1.2 : ℂ)) * f ((kk q.1)⁻¹ * U a₁ a₂ ha q.2 * kk q.1)

theorem continuous_Hf {f : GL (Fin 2) ℂ → ℂ} (hf : Continuous f) : Continuous (Hf a₁ a₂ ha f) := by
  unfold Hf
  refine Continuous.mul ?_ (hf.comp ?_)
  · exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (by fun_prop))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (by fun_prop)))
  · exact ((continuous_kk.comp continuous_fst).inv.mul ((continuous_U a₁ a₂ ha).comp continuous_snd)).mul
      (continuous_kk.comp continuous_fst)

def BOX : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi))

def BOXc : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Set.Icc 0 Real.pi ×ˢ Set.Icc 0 (Real.pi / 2)) ×ˢ (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))

theorem BOX_subset_BOXc : BOX ⊆ BOXc :=
  Set.prod_mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
    (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)

theorem isCompact_BOXc : IsCompact BOXc :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

theorem measurableSet_BOX : MeasurableSet BOX :=
  (measurableSet_Ioo.prod measurableSet_Ioo).prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem integrable_Hf {f : GL (Fin 2) ℂ → ℂ} (hf : Continuous f) (ρ : ℝ)
    (hρ : ∀ (r : (ℝ × ℝ) × (ℝ × ℝ)) (v : ℂ), f ((kk r)⁻¹ * U a₁ a₂ ha v * kk r) ≠ 0 → ‖v‖ ≤ ρ) :
    Integrable (Hf a₁ a₂ ha f) ((volume.restrict BOX).prod volume) := by
  have hK : IsCompact (BOXc ×ˢ Metric.closedBall (0 : ℂ) ρ) := isCompact_BOXc.prod (isCompact_closedBall _ _)
  have h1 : IntegrableOn (Hf a₁ a₂ ha f) (BOXc ×ˢ Metric.closedBall (0 : ℂ) ρ) volume :=
    (continuous_Hf a₁ a₂ ha hf).continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (Hf a₁ a₂ ha f) (BOX ×ˢ (Set.univ : Set ℂ)) volume := by
    refine h1.of_forall_diff_eq_zero (measurableSet_BOX.prod MeasurableSet.univ) fun q hq => ?_
    have hq1 : q.1 ∈ BOX := hq.1.1
    have hq2 : q ∉ BOXc ×ˢ Metric.closedBall (0 : ℂ) ρ := hq.2
    have hv : ¬ ‖q.2‖ ≤ ρ := fun h => hq2 ⟨BOX_subset_BOXc hq1, by simpa using h⟩
    unfold Hf
    by_contra hne
    exact hv (hρ _ _ (right_ne_zero_of_mul hne))
  have hμ : ((volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict BOX).prod (volume : Measure ℂ) =
      (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℂ)).restrict (BOX ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod ((ℝ × ℝ) × (ℝ × ℝ)) ℂ, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hμ]
  exact h2

theorem integral_comp_mul_left_complex (c : ℂ) (hc : c ≠ 0) (g : ℂ → ℂ) :
    ∫ z : ℂ, g (c * z) = ((Complex.normSq c)⁻¹ : ℝ) * ∫ v : ℂ, g v := by
  have hdet : LinearMap.det (LinearMap.mul ℝ ℂ c) = Complex.normSq c :=
    (Algebra.norm_apply ℝ c).symm.trans (Algebra.norm_complex_apply c)
  have hdet0 : LinearMap.det (LinearMap.mul ℝ ℂ c) ≠ 0 := by
    rw [hdet]; exact (Complex.normSq_pos.2 hc).ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ)) hdet0
  set e : ℂ ≃ᵐ ℂ := (Homeomorph.mulLeft₀ c hc).toMeasurableEquiv with he
  have hecoe : (e : ℂ → ℂ) = fun z => c * z := rfl
  have h1 : ∫ z : ℂ, g (c * z) = ∫ v, g v ∂(Measure.map e volume) := by
    rw [integral_map_equiv]
    rfl
  rw [h1, hecoe]
  have hcoe : (fun z : ℂ => c * z) = (LinearMap.mul ℝ ℂ c : ℂ → ℂ) := by
    funext z; rfl
  rw [hcoe, hmap, integral_smul_measure, hdet, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.real_smul]

def A₁ (t : ℝ) : ℝ := ρ₀ (t * |t|) / max t 1

theorem continuous_A₁ : Continuous A₁ := by
  unfold A₁
  refine Continuous.div (continuous_ρ₀.comp (continuous_id.mul continuous_abs)) (by fun_prop) fun t => ?_
  exact (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne'

theorem A₁_nonneg (t : ℝ) : 0 ≤ A₁ t :=
  div_nonneg (ρ₀_nonneg _) (le_trans zero_le_one (le_max_right _ _))

theorem A₁_eq_of_pos {t : ℝ} (ht : 0 < t) : ρ₀ (t ^ 2) / t = A₁ t := by
  unfold A₁
  rw [abs_of_pos ht, ← sq]
  by_cases h1 : 1 ≤ t
  · rw [max_eq_left h1]
  · rw [not_le] at h1
    have : ρ₀ (t ^ 2) = 0 := by
      by_contra hne
      have := (ρ₀_ne_zero_imp hne).1
      nlinarith
    rw [this, zero_div, zero_div]

theorem A₁_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : A₁ t = 0 := by
  unfold A₁
  have : ρ₀ (t * |t|) = 0 := by
    by_contra hne
    have h1 := (ρ₀_ne_zero_imp hne).1
    have : t * |t| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht (abs_nonneg _)
    linarith
  rw [this, zero_div]

theorem hasCompactSupport_A₁ : HasCompactSupport A₁ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun t ht => ?_
  unfold A₁
  have : ρ₀ (t * |t|) = 0 := by
    by_contra hne
    obtain ⟨h1, h2⟩ := ρ₀_ne_zero_imp hne
    apply ht
    rw [Set.mem_Icc]
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h] at h1 h2
      constructor <;> nlinarith
    · rw [abs_of_neg h] at h1
      nlinarith
  rw [this, zero_div]

theorem integral_A₁_pos : 0 < ∫ t, A₁ t := by
  have h32 : A₁ (Real.sqrt (3 / 2)) ≠ 0 := by
    have hs : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
    rw [← A₁_eq_of_pos hs, Real.sq_sqrt (by norm_num), ρ₀_three_halves]
    exact div_ne_zero (by norm_num) hs.ne'
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero continuous_A₁ hasCompactSupport_A₁
    A₁_nonneg h32

variable (τ : Measure[centralizerBorel ℂ γ] (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))))

def Af (β : ℂ) : ℝ := 2 * A₁ β.re * A₁ β.im / Cτ γ τ

def IAr : ℝ := ∫ β in Qpos, Af γ τ β

theorem IAr_eq : IAr γ τ = 2 / Cτ γ τ * (∫ t, A₁ t) ^ 2 := by
  unfold IAr Af
  have h1 : ∫ β in Qpos, 2 * A₁ β.re * A₁ β.im / Cτ γ τ = ∫ β : ℂ, 2 * A₁ β.re * A₁ β.im / Cτ γ τ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun β hβ => ?_
    simp only [Qpos, Set.mem_setOf_eq, not_and_or, not_lt] at hβ
    rcases hβ with h | h
    · rw [A₁_eq_zero_of_nonpos h]; ring
    · rw [A₁_eq_zero_of_nonpos h]; ring
  rw [h1]
  have h2 : ∫ β : ℂ, 2 * A₁ β.re * A₁ β.im / Cτ γ τ =
      ∫ q : ℝ × ℝ, 2 / Cτ γ τ * (A₁ q.1 * A₁ q.2) := by
    rw [← (Complex.volume_preserving_equiv_real_prod).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
    simp only [Complex.measurableEquivRealProd_apply]
    ring
  rw [h2, integral_const_mul, Measure.volume_eq_prod, integral_prod_mul, sq]

theorem IAr_pos {a₁ a₂ : ℂ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂]) (hne : a₁ ≠ a₂)
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) : 0 < IAr γ τ := by
  rw [IAr_eq]
  exact mul_pos (div_pos two_pos (Cτ_pos hγ hne τ hτ)) (pow_pos integral_A₁_pos 2)

def Bf (f : GL (Fin 2) ℂ → ℂ) (R : ℝ) (w : (ℂ × ℂ) × ℂ) : ℂ :=
  ((Real.sin w.1.1.im : ℂ) * (Real.cos w.1.1.im : ℂ)) *
    ((χc R (Complex.normSq w.2) : ℂ) * f ((ka w.1)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * w.2) * ka w.1))

def Ξ (f : GL (Fin 2) ℂ → ℂ) (R : ℝ) (q : (ℂ × ℂ) × (ℂ × ℂ)) : ℂ :=
  (Af γ τ q.2.1 : ℂ) * Bf a₁ a₂ ha f R (q.1, q.2.2)

def Ewin : Set ((ℂ × ℂ) × (ℂ × ℂ)) := (W₀ ×ˢ W₁) ×ˢ (Qpos ×ˢ (Set.univ : Set ℂ))

theorem measurableSet_Ewin : MeasurableSet Ewin :=
  (isOpen_W₀.measurableSet.prod isOpen_W₁.measurableSet).prod (isOpen_Qpos.measurableSet.prod MeasurableSet.univ)

def wtq (q : (ℂ × ℂ) × (ℂ × ℂ)) : ℝ := 2 * Real.sin q.1.1.im * Real.cos q.1.1.im / (q.2.1.re * q.2.1.im)

def chartq (q : (ℂ × ℂ) × (ℂ × ℂ)) : GL (Fin 2) ℂ :=
  if h : 0 < q.2.1.re ∧ 0 < q.2.1.im then
    twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
      unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im
  else 1

include hγ in

theorem chart_integrand_eq (f : GL (Fin 2) ℂ → ℂ) (R : ℝ) (q : (ℂ × ℂ) × (ℂ × ℂ)) (hq : q ∈ Ewin) :
    (wtq q : ℂ) * (f ((chartq q)⁻¹ * γ * chartq q) * (probe γ τ R (chartq q) : ℂ)) =
      Ξ a₁ a₂ ha γ τ f R q := by
  obtain ⟨-, ⟨hb1, hb2⟩, -⟩ := hq
  have hguard : 0 < q.2.1.re ∧ 0 < q.2.1.im := ⟨hb1, hb2⟩
  have hchart : chartq q =
      twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos hguard.1 2, pow_pos hguard.2 2⟩ *
        unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im := by
    unfold chartq; rw [dif_pos hguard]
  rw [hchart, splitElt_conj a₁ a₂ ha γ hγ _ _ _ hguard]

  have hprobe : probe γ τ R (twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2)
        ⟨pow_pos hguard.1 2, pow_pos hguard.2 2⟩ * unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im) =
      ρ₀ (q.2.1.re ^ 2) * ρ₀ (q.2.1.im ^ 2) * χc R (Complex.normSq q.2.2) / Cτ γ τ := by
    unfold probe
    rw [Dq_mul_unitaryElt, Qq_mul_unitaryElt, Pq_mul_unitaryElt, Dq_splitElt _ _ _ hguard,
      Qq_splitElt _ _ _ hguard, Pq_splitElt _ _ _ hguard]
    have h1 : (q.2.1.re * q.2.1.im) ^ 2 / q.2.1.im ^ 2 = q.2.1.re ^ 2 := by
      field_simp
    have h2 : (q.2.1.re * q.2.1.im) ^ 2 * Complex.normSq q.2.2 / (q.2.1.re * q.2.1.im) ^ 2 =
        Complex.normSq q.2.2 := by
      field_simp
    rw [h1, h2]
  rw [hprobe]
  unfold Ξ Af Bf ka wtq
  rw [← A₁_eq_of_pos hb1, ← A₁_eq_of_pos hb2]
  push_cast
  have hb1' : (q.2.1.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb1.ne'
  have hb2' : (q.2.1.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb2.ne'
  field_simp

def rr : (ℂ × ℂ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  MeasurableEquiv.prodCongr Complex.measurableEquivRealProd Complex.measurableEquivRealProd

theorem rr_apply (a : ℂ × ℂ) : rr a = ((a.1.re, a.1.im), (a.2.re, a.2.im)) := rfl

theorem measurePreserving_rr : MeasurePreserving rr volume volume := by
  have h := (Complex.volume_preserving_equiv_real_prod).prod (Complex.volume_preserving_equiv_real_prod)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h
  exact h

theorem Wang_eq : (W₀ ×ˢ W₁ : Set (ℂ × ℂ)) = rr ⁻¹' BOX := by
  ext a
  simp only [W₀, W₁, BOX, Set.mem_prod, Set.mem_setOf_eq, Set.mem_preimage, rr_apply, Set.mem_Ioo]
  tauto

variable {a₁ a₂ γ}

include hγ in

theorem final
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ)
    (H1 : ∃ c : ℝ, 0 < c ∧ ∀ F : GL (Fin 2) ℂ → ℂ, Measurable[glBorelOf ℂ] F → Integrable F μ →
      IntegrableOn (fun q => (wtq q : ℂ) * F (chartq q)) Ewin volume ∧
        ∫ g, F g ∂μ = (c : ℂ) * ∫ q in Ewin, (wtq q : ℂ) * F (chartq q))
    (H2 : ∀ F : GL (Fin 2) ℂ → ℂ, Continuous F →
      unitaryAverage F = (1 / (2 * Real.pi ^ 3) : ℂ) *
        ∫ r in BOX, (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ f : GL (Fin 2) ℂ → ℂ, Continuous f → HasCompactSupport f →
        ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I →
          I = (κ : ℂ) * ∫ v : ℂ, unitaryAverage (fun k =>
            if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
              f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) := by
  letI : MeasurableSpace (GL (Fin 2) ℂ) := glBorelOf ℂ
  haveI : BorelSpace (GL (Fin 2) ℂ) := borelSpace_glBorelOf ℂ
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := centralizerBorel ℂ γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) := ⟨rfl⟩
  haveI := hμ
  haveI := hτ
  have ha : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
  have hsub : a₁ - a₂ ≠ 0 := sub_ne_zero.2 hne
  set δ : ℝ := Complex.normSq (a₁ - a₂) with hδ
  have hδpos : 0 < δ := Complex.normSq_pos.2 hsub
  obtain ⟨c, hc, hchart⟩ := H1
  have hC := Cτ_pos hγ hne τ hτ
  have hIA := IAr_pos (γ := γ) τ hγ hne hτ
  refine ⟨2 * Real.pi ^ 3 * c * IAr γ τ / δ, by positivity, fun f hf hfc I hI => ?_⟩

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ g ∈ tsupport f,
      (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖) ^ 2 ≤ M := by
    have hcont : Continuous fun g : GL (Fin 2) ℂ =>
        (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖) ^ 2 :=
      ((continuous_glEntry 0 1).norm.add (continuous_glEntry 1 0).norm).pow 2
    obtain ⟨M, hM⟩ := hfc.isCompact.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨M, fun g hg => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM g hg))⟩
  set R : ℝ := max M 0 / δ with hRdef
  have hR0 : 0 ≤ R := div_nonneg (le_max_right _ _) hδpos.le
  have hR : ∀ x : GL (Fin 2) ℂ, f (x⁻¹ * γ * x) ≠ 0 → Pq x / Dq x ≤ R := by
    intro x hx
    have hmem : x⁻¹ * γ * x ∈ tsupport f := subset_tsupport _ (Function.mem_support.2 hx)
    have h1 := sq_Pq_le a₁ a₂ γ x hγ
    have h2 := hM _ hmem
    have hD := Dq_pos x
    rw [hRdef, div_le_div_iff₀ hD hδpos]
    have h3 : (‖((x⁻¹ * γ * x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ +
        ‖((x⁻¹ * γ * x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖) ^ 2 * Dq x ≤ max M 0 * Dq x :=
      mul_le_mul_of_nonneg_right (h2.trans (le_max_left _ _)) hD.le
    nlinarith
  have hρz : ∀ (k : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) (z : ℂ), k = unitaryElt ψ η ξ₁ ξ₂ →
      f (k⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * k) ≠ 0 → Complex.normSq z ≤ R := by
    intro k ψ η ξ₁ ξ₂ z hk hv
    have h11 : (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 := ⟨one_pos, one_pos⟩
    have hconj := splitElt_conj a₁ a₂ ha γ hγ 1 1 z h11 k
    have hx := hR (twistedSplitElt ((1 : ℝ) ^ 2) ((1 : ℝ) ^ 2) ((1 : ℝ) * z) ⟨pow_pos h11.1 2, pow_pos h11.2 2⟩ * k)
      (by rw [hconj]; exact hv)
    rw [hk, Pq_mul_unitaryElt, Dq_mul_unitaryElt, Pq_splitElt _ _ _ h11, Dq_splitElt _ _ _ h11] at hx
    simpa using hx
  have hρ : ∀ (k : GL (Fin 2) ℂ) (ψ η ξ₁ ξ₂ : ℝ) (v : ℂ), k = unitaryElt ψ η ξ₁ ξ₂ →
      f (k⁻¹ * U a₁ a₂ ha v * k) ≠ 0 → ‖v‖ ≤ Real.sqrt (δ * R) := by
    intro k ψ η ξ₁ ξ₂ v hk hv
    have hvz : (a₁ - a₂) * (v / (a₁ - a₂)) = v := mul_div_cancel₀ _ hsub
    have h1 := hρz k ψ η ξ₁ ξ₂ (v / (a₁ - a₂)) hk (by rw [hvz]; exact hv)
    have h2 : Complex.normSq v ≤ δ * R := by
      rw [← hvz, Complex.normSq_mul]
      exact mul_le_mul_of_nonneg_left h1 (Complex.normSq_nonneg _)
    rw [Complex.norm_def]
    exact Real.sqrt_le_sqrt h2

  have hsec : IsSectionFnOn ℂ γ τ f (probe γ τ R) := by
    refine ⟨probe_nonneg γ τ hγ hne hτ R, (continuous_probe γ τ R).measurable, hasCompactSupport_probe γ τ R hR0,
      fun x hx => ?_⟩
    have h := integral_probe_translate γ τ hγ hne hτ R x
    rw [χc_eq_one (hR x hx)] at h
    exact h
  set I₀ : ℂ := ∫ x, f (x⁻¹ * γ * x) * (probe γ τ R x : ℂ) ∂μ with hI₀def
  have hI₀ : IsOrbitalIntegralOn ℂ μ γ τ f I₀ := ⟨probe γ τ R, hsec, rfl⟩
  have hreg : IsRegularSemisimple γ := by
    rw [isRegularSemisimple_iff_ne_zero, hγ, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    have : (a₁ + a₂) ^ 2 - 4 * (a₁ * a₂ - 0 * 0) = (a₁ - a₂) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero 2 hsub
  have hfb : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := hf.bounded_above_of_compact_support hfc
  have hIeq : I = I₀ :=
    AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple ℂ μ hμ γ hreg τ hτ f hf.measurable hfb hI hI₀
  rw [hIeq, hI₀def]

  set Φ : GL (Fin 2) ℂ → ℂ := fun x => f (x⁻¹ * γ * x) * (probe γ τ R x : ℂ) with hΦdef
  have hconjc : Continuous fun x : GL (Fin 2) ℂ => x⁻¹ * γ * x := (continuous_inv.mul continuous_const).mul continuous_id
  have hΦc : Continuous Φ :=
    (hf.comp hconjc).mul (Complex.continuous_ofReal.comp (continuous_probe γ τ R))
  have hΦs : HasCompactSupport Φ := by
    have h1 : HasCompactSupport (fun x => (probe γ τ R x : ℂ)) :=
      (hasCompactSupport_probe γ τ R hR0).comp_left Complex.ofReal_zero
    exact h1.mul_left
  obtain ⟨hint1, hI1⟩ := hchart Φ hΦc.measurable (hΦc.integrable_of_hasCompactSupport hΦs)
  rw [show (∫ x, f (x⁻¹ * γ * x) * (probe γ τ R x : ℂ) ∂μ) = ∫ x, Φ x ∂μ from rfl, hI1]

  set E : Set ((ℂ × ℂ) × (ℂ × ℂ)) := (W₀ ×ˢ W₁) ×ˢ (Qpos ×ˢ (Set.univ : Set ℂ)) with hE
  have hEE : Ewin = E := rfl
  have hptw : ∀ q ∈ Ewin, (wtq q : ℂ) * Φ (chartq q) = Ξ a₁ a₂ ha γ τ f R q := fun q hq =>
    chart_integrand_eq a₁ a₂ ha γ hγ τ f R q hq
  have hI2 : ∫ q in Ewin, (wtq q : ℂ) * Φ (chartq q) = ∫ q in E, Ξ a₁ a₂ ha γ τ f R q := by
    rw [setIntegral_congr_fun measurableSet_Ewin hptw, hEE]
  have hintΞ : IntegrableOn (Ξ a₁ a₂ ha γ τ f R) E volume := by
    have h := hint1.congr_fun hptw measurableSet_Ewin
    rw [hEE] at h
    exact h
  rw [hI2]

  have hI3 : ∫ q in E, Ξ a₁ a₂ ha γ τ f R q =
      (IAr γ τ : ℂ) * ∫ a in W₀ ×ˢ W₁, ∫ z, Bf a₁ a₂ ha f R (a, z) := by
    have hint' : Integrable (Ξ a₁ a₂ ha γ τ f R)
        ((volume.restrict (W₀ ×ˢ W₁)).prod (volume.restrict (Qpos ×ˢ (Set.univ : Set ℂ)))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hintΞ
    rw [hE, Measure.volume_eq_prod (ℂ × ℂ) (ℂ × ℂ), ← Measure.prod_restrict, integral_prod _ hint']
    have hinner : ∀ a : ℂ × ℂ, ∫ w in Qpos ×ˢ (Set.univ : Set ℂ), Ξ a₁ a₂ ha γ τ f R (a, w) =
        (IAr γ τ : ℂ) * ∫ z, Bf a₁ a₂ ha f R (a, z) := by
      intro a
      rw [Measure.volume_eq_prod ℂ ℂ, ← Measure.prod_restrict, Measure.restrict_univ]
      unfold Ξ
      rw [integral_prod_mul (fun β : ℂ => (Af γ τ β : ℂ)) (fun z : ℂ => Bf a₁ a₂ ha f R (a, z)),
        integral_complex_ofReal]
      rfl
    simp_rw [hinner]
    rw [integral_const_mul]
  rw [hI3]

  have hI4 : ∀ a : ℂ × ℂ, ∫ z, Bf a₁ a₂ ha f R (a, z) =
      ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) * ((δ⁻¹ : ℝ) : ℂ) *
        ∫ v, f ((ka a)⁻¹ * U a₁ a₂ ha v * ka a) := by
    intro a
    have hfun : (fun z : ℂ => (χc R (Complex.normSq z) : ℂ) * f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a)) =
        fun z => f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a) := by
      funext z
      by_cases hz : f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a) = 0
      · rw [hz, mul_zero]
      · rw [χc_eq_one (hρz (ka a) a.1.re a.1.im a.2.re a.2.im z rfl hz), Complex.ofReal_one, one_mul]
    calc ∫ z, Bf a₁ a₂ ha f R (a, z)
        = ∫ z, ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) *
            ((χc R (Complex.normSq z) : ℂ) * f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a)) := rfl
      _ = ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) *
            ∫ z, (χc R (Complex.normSq z) : ℂ) * f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a) :=
          integral_const_mul _ _
      _ = ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) * ∫ z, f ((ka a)⁻¹ * U a₁ a₂ ha ((a₁ - a₂) * z) * ka a) := by
          rw [hfun]
      _ = ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) *
            (((δ⁻¹ : ℝ) : ℂ) * ∫ v, f ((ka a)⁻¹ * U a₁ a₂ ha v * ka a)) := by
          have h := integral_comp_mul_left_complex (a₁ - a₂) hsub (fun v => f ((ka a)⁻¹ * U a₁ a₂ ha v * ka a))
          rw [h]
      _ = _ := by ring
  simp_rw [hI4]

  have hint_Hf := integrable_Hf a₁ a₂ ha hf (Real.sqrt (δ * R))
    (fun r v hv => hρ (kk r) r.1.1 r.1.2 r.2.1 r.2.2 v rfl hv)
  have hI5 : ∫ a in W₀ ×ˢ W₁, ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) * ((δ⁻¹ : ℝ) : ℂ) *
        ∫ v, f ((ka a)⁻¹ * U a₁ a₂ ha v * ka a) =
      ((δ⁻¹ : ℝ) : ℂ) * ∫ q in BOX ×ˢ (Set.univ : Set ℂ), Hf a₁ a₂ ha f q := by
    have h1 : ∫ a in W₀ ×ˢ W₁, ((Real.sin a.1.im : ℂ) * (Real.cos a.1.im : ℂ)) * ((δ⁻¹ : ℝ) : ℂ) *
          ∫ v, f ((ka a)⁻¹ * U a₁ a₂ ha v * ka a) =
        ∫ r in BOX, ((δ⁻¹ : ℝ) : ℂ) * ∫ v, Hf a₁ a₂ ha f (r, v) := by
      rw [Wang_eq]
      have h := measurePreserving_rr.setIntegral_preimage_emb rr.measurableEmbedding
        (fun r : (ℝ × ℝ) × (ℝ × ℝ) => ((δ⁻¹ : ℝ) : ℂ) * ∫ v, Hf a₁ a₂ ha f (r, v)) BOX
      rw [← h]
      refine setIntegral_congr_fun (rr.measurable measurableSet_BOX) fun a _ => ?_
      simp only [Hf, rr_apply, kk, ka]
      rw [integral_const_mul]
      ring
    rw [h1, integral_const_mul]
    congr 1
    have hμ' : ((volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict BOX).prod (volume : Measure ℂ) =
        (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℂ)).restrict (BOX ×ˢ Set.univ) := by
      rw [Measure.volume_eq_prod ((ℝ × ℝ) × (ℝ × ℝ)) ℂ, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [show (∫ q in BOX ×ˢ (Set.univ : Set ℂ), Hf a₁ a₂ ha f q) =
        ∫ q, Hf a₁ a₂ ha f q ∂(((volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict BOX).prod (volume : Measure ℂ))
      by rw [hμ'], integral_prod _ hint_Hf]
  rw [hI5]

  have hI6 : ∫ q in BOX ×ˢ (Set.univ : Set ℂ), Hf a₁ a₂ ha f q =
      ∫ v, (2 * Real.pi ^ 3 : ℂ) * unitaryAverage (fun k => f (k⁻¹ * U a₁ a₂ ha v * k)) := by
    have hμ' : ((volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict BOX).prod (volume : Measure ℂ) =
        (volume : Measure (((ℝ × ℝ) × (ℝ × ℝ)) × ℂ)).restrict (BOX ×ˢ Set.univ) := by
      rw [Measure.volume_eq_prod ((ℝ × ℝ) × (ℝ × ℝ)) ℂ, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [show (∫ q in BOX ×ˢ (Set.univ : Set ℂ), Hf a₁ a₂ ha f q) =
        ∫ q, Hf a₁ a₂ ha f q ∂(((volume : Measure ((ℝ × ℝ) × (ℝ × ℝ))).restrict BOX).prod (volume : Measure ℂ))
      by rw [hμ'], integral_prod_symm _ hint_Hf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hcv : Continuous fun k : GL (Fin 2) ℂ => f (k⁻¹ * U a₁ a₂ ha v * k) :=
      hf.comp ((continuous_inv.mul continuous_const).mul continuous_id)
    show (∫ r in BOX, Hf a₁ a₂ ha f (r, v)) = (2 * Real.pi ^ 3 : ℂ) * unitaryAverage (fun k => f (k⁻¹ * U a₁ a₂ ha v * k))
    rw [H2 _ hcv]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    rw [← mul_assoc, show (2 * (Real.pi : ℂ) ^ 3) * (1 / (2 * Real.pi ^ 3)) = 1 by field_simp, one_mul]
    rfl
  rw [hI6, integral_const_mul]

  have hdet : ∀ v : ℂ, Matrix.det !![a₁, v; 0, a₂] ≠ 0 := fun v => by rw [det_upper]; exact ha
  have hfun : (fun v : ℂ => unitaryAverage fun k =>
      if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) =
      fun v => unitaryAverage fun k => f (k⁻¹ * U a₁ a₂ ha v * k) := by
    funext v
    congr 1
    funext k
    rw [dif_pos (hdet v)]
    rfl
  rw [hfun]
  push_cast
  ring

end Assembly

end P2mOIDiagC
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage.P2mOIDiagC"

open AutomorphicForm P2mOIDiagC in
theorem solution
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (a₁ a₂ : ℂ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (γ : GL (Fin 2) ℂ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ f : GL (Fin 2) ℂ → ℂ, Continuous f → HasCompactSupport f →
        ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I →
          I = (κ : ℂ) * ∫ v : ℂ, unitaryAverage (fun k =>
            if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
              f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) :=
  final hγ τ μ hμ ha₁ ha₂ hne hτ
    (AutomorphicForm.GL2Twisted.exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart μ hμ)
    (fun F hF => AutomorphicForm.GL2Twisted.unitaryAverage_eq_mul_setIntegral_of_continuous F hF)

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage.P2mOIDiagC"

end S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage (solution)
