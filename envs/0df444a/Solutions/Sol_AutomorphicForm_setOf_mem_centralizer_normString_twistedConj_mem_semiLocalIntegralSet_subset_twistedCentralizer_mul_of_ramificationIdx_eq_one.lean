-- Prove2me | solution 1 for AutomorphicForm.setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3f5900b2-1ff6-53c2-95f8-c5a21f9beb46

import Theorems.Thm_AutomorphicForm_exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct TensorProduct.RightActions Pointwise IsMulCommutative Valued
open NumberField IsDedekindDomain

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal

noncomputable section

namespace P2mTwistedTorusUnram

section Algebra

variable {R : Type*} [CommRing R]

variable {K L v σ δ} in

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) R) (h : X * g = g * X) (u : R)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem smul_one_mul' (a : R) (M : Matrix (Fin 2) (Fin 2) R) : (a • (1 : Matrix (Fin 2) (Fin 2) R)) * M = a • M :=
  smul_one_mul _ _

theorem mul_smul_one' (a : R) (M : Matrix (Fin 2) (Fin 2) R) : M * (a • (1 : Matrix (Fin 2) (Fin 2) R)) = a • M :=
  by rw [Matrix.mul_smul, mul_one]

theorem smul_smul' (a b : R) (M : Matrix (Fin 2) (Fin 2) R) : a • b • M = (a * b) • M := smul_smul a b M

theorem disc_eq (g : Matrix (Fin 2) (Fin 2) R) :
    g.trace ^ 2 - 4 * g.det = (g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem smul_one_add_smul_apply (g : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 0 0 = a + b * g 0 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 0 1 = b * g 0 1 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 1 0 = b * g 1 0 ∧
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) 1 1 = a + b * g 1 1 := by
  simp [Matrix.add_apply, Matrix.smul_apply]

theorem matrix_eq_of_entries {X Y : Matrix (Fin 2) (Fin 2) R} (h00 : X 0 0 = Y 0 0) (h01 : X 0 1 = Y 0 1)
    (h10 : X 1 0 = Y 1 0) (h11 : X 1 1 = Y 1 1) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem exists_eq_smul_one_add_smul (g X : Matrix (Fin 2) (Fin 2) R) (h : X * g = g * X)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) :
    ∃ a b : R, X = a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  obtain ⟨h1, h2, h3⟩ := entries_of_commute g X h u hu
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) with hp
  refine ⟨X 0 0 - p * g 0 0, p, ?_⟩
  obtain ⟨y00, y01, y10, y11⟩ := smul_one_add_smul_apply g (X 0 0 - p * g 0 0) p
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [y00]; ring
  · rw [y01]; exact h1
  · rw [y10]; exact h2
  · rw [y11]; linear_combination (-1 : R) * h3

theorem mul_comm_of_commute (g X Y : Matrix (Fin 2) (Fin 2) R) (hX : X * g = g * X) (hY : Y * g = g * Y)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) : X * Y = Y * X := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g X hX u hu
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g Y hY u hu
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

theorem eq_zero_of_sq_eq_zero [IsReduced R] (g : Matrix (Fin 2) (Fin 2) R)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) {a b : R}
    (h : (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) * (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  set X := a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g with hX
  obtain ⟨x00, x01, x10, x11⟩ := smul_one_add_smul_apply g a b
  rw [← hX] at x00 x01 x10 x11
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at e00 e01 e10 e11
  simp only [x00, x01, x10, x11] at e00 e01 e10 e11
  set β := b * (2 * a + b * (g 0 0 + g 1 1)) with hβ
  have c1 : β * g 0 1 = 0 := by linear_combination e01
  have c3 : β * (g 0 0 - g 1 1) = 0 := by linear_combination e00 - e11
  have c4 : β ^ 2 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 0 := by
    linear_combination (β * (g 0 0 - g 1 1)) * c3 + (4 * β * g 1 0) * c1
  have hβ2 : β ^ 2 = 0 := by linear_combination (-(β ^ 2)) * hu + u * c4
  have c5 : b ^ 2 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) + (2 * a + b * (g 0 0 + g 1 1)) ^ 2 = 0 := by
    linear_combination 2 * e00 + 2 * e11
  have c6 : b ^ 4 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 0 := by
    linear_combination b ^ 2 * c5 - hβ2
  have hb4 : b ^ 4 = 0 := by linear_combination (-(b ^ 4)) * hu + u * c6
  have hb : b = 0 := IsReduced.eq_zero b ⟨4, hb4⟩
  subst hb
  have ha2 : a ^ 2 = 0 := by linear_combination e00
  exact ⟨IsReduced.eq_zero a ⟨2, ha2⟩, rfl⟩

theorem eq_zero_of_smul_one_add_smul_eq_zero [IsReduced R] (g : Matrix (Fin 2) (Fin 2) R)
    (hγ : IsUnit (g.trace ^ 2 - 4 * g.det)) {α β : R} (h : α • (1 : Matrix (Fin 2) (Fin 2) R) + β • g = 0) :
    α = 0 ∧ β = 0 := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  rw [disc_eq] at hu
  obtain ⟨x00, x01, x10, x11⟩ := smul_one_add_smul_apply g α β
  rw [h] at x00 x01 x10 x11
  simp only [Matrix.zero_apply] at x00 x01 x10 x11
  have c1 : β * g 0 1 = 0 := x01.symm
  have c3 : β * (g 0 0 - g 1 1) = 0 := by linear_combination x11 - x00
  have c4 : β ^ 2 * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 0 := by
    linear_combination (β * (g 0 0 - g 1 1)) * c3 + (4 * β * g 1 0) * c1
  have hβ2 : β ^ 2 = 0 := by linear_combination (-(β ^ 2)) * hu + u * c4
  have hβ : β = 0 := IsReduced.eq_zero β ⟨2, hβ2⟩
  subst hβ
  refine ⟨?_, rfl⟩
  linear_combination -x00

theorem smul_one_add_smul_mul_self (g : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) * (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) =
      (a * a - b * b * g.det) • (1 : Matrix (Fin 2) (Fin 2) R) + (2 * a * b + b * b * g.trace) • g := by
  obtain ⟨x00, x01, x10, x11⟩ := smul_one_add_smul_apply g a b
  obtain ⟨y00, y01, y10, y11⟩ := smul_one_add_smul_apply g (a * a - b * b * g.det) (2 * a * b + b * b * g.trace)
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [y00]; simp only [Matrix.mul_apply, Fin.sum_univ_two, x00, x01, x10, x11]; rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring
  · rw [y01]; simp only [Matrix.mul_apply, Fin.sum_univ_two, x00, x01, x10, x11]; rw [Matrix.trace_fin_two]; ring
  · rw [y10]; simp only [Matrix.mul_apply, Fin.sum_univ_two, x00, x01, x10, x11]; rw [Matrix.trace_fin_two]; ring
  · rw [y11]; simp only [Matrix.mul_apply, Fin.sum_univ_two, x00, x01, x10, x11]; rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem smul_one_add_smul_commute (g : Matrix (Fin 2) (Fin 2) R) (a b : R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) * g = g * (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) := by
  rw [add_mul, mul_add, smul_one_mul', mul_smul_one', smul_mul_assoc, mul_smul_comm]

theorem smul_smul_one_add_smul (g : Matrix (Fin 2) (Fin 2) R) (c a b : R) :
    c • (a • (1 : Matrix (Fin 2) (Fin 2) R) + b • g) = (c * a) • (1 : Matrix (Fin 2) (Fin 2) R) + (c * b) • g := by
  rw [smul_add, smul_smul, smul_smul]

def conjM (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R := X.trace • (1 : Matrix (Fin 2) (Fin 2) R) - X

theorem conjM_apply (X : Matrix (Fin 2) (Fin 2) R) :
    conjM X 0 0 = X 1 1 ∧ conjM X 0 1 = -X 0 1 ∧ conjM X 1 0 = -X 1 0 ∧ conjM X 1 1 = X 0 0 := by
  simp [conjM, Matrix.sub_apply, Matrix.smul_apply, Matrix.trace_fin_two]

theorem conjM_add (X Y : Matrix (Fin 2) (Fin 2) R) : conjM (X + Y) = conjM X + conjM Y := by
  simp only [conjM, Matrix.trace_add, add_smul]; abel

theorem conjM_one : conjM (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := conjM_apply (1 : Matrix (Fin 2) (Fin 2) R)
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [h00]; simp
  · rw [h01]; simp
  · rw [h10]; simp
  · rw [h11]; simp

theorem conjM_mul_of_commute (X Y : Matrix (Fin 2) (Fin 2) R) (h : X * Y = Y * X) :
    conjM (X * Y) = conjM X * conjM Y := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  obtain ⟨x00, x01, x10, x11⟩ := conjM_apply X
  obtain ⟨y00, y01, y10, y11⟩ := conjM_apply Y
  obtain ⟨z00, z01, z10, z11⟩ := conjM_apply (X * Y)
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [z00, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, x00, x01, y00, y10]
    linear_combination e11
  · rw [z01, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, x00, x01, y01, y11]
    linear_combination -e01
  · rw [z10, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, x10, x11, y00, y10]
    linear_combination -e10
  · rw [z11, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, x10, x11, y01, y11]
    linear_combination e00

theorem conjM_conjM (X : Matrix (Fin 2) (Fin 2) R) : conjM (conjM X) = X := by
  obtain ⟨x00, x01, x10, x11⟩ := conjM_apply X
  obtain ⟨z00, z01, z10, z11⟩ := conjM_apply (conjM X)
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [z00, x11]
  · rw [z01, x01, neg_neg]
  · rw [z10, x10, neg_neg]
  · rw [z11, x00]

theorem conjM_smul_one (a : R) : conjM (a • (1 : Matrix (Fin 2) (Fin 2) R)) = a • (1 : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨z00, z01, z10, z11⟩ := conjM_apply (a • (1 : Matrix (Fin 2) (Fin 2) R))
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_
  · rw [z00]; simp
  · rw [z01]; simp
  · rw [z10]; simp
  · rw [z11]; simp

theorem add_conjM (X : Matrix (Fin 2) (Fin 2) R) : X + conjM X = X.trace • (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [conjM, add_sub_cancel]

theorem conjM_commute {g X : Matrix (Fin 2) (Fin 2) R} (h : X * g = g * X) : conjM X * g = g * conjM X := by
  rw [conjM, sub_mul, mul_sub, smul_one_mul', mul_smul_one', h]

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[k] y =
      Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ',
            AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaTensor_iterate_of_pow_eq_one {m : ℕ} (hm : σ ^ m = 1) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[m] y = y := by
  rw [sigmaTensor_iterate, hm]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaGL_apply_val (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((AutomorphicForm.sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) i j =
      AutomorphicForm.sigmaTensor K L A σ ((x : Matrix (Fin 2) (Fin 2) _) i j) := rfl

theorem sigmaGL_iterate_of_pow_eq_one {m : ℕ} (hm : σ ^ m = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[m] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j =
        (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AutomorphicForm.sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← AutomorphicForm.sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate_of_pow_eq_one K L A σ hm]

theorem sigmaGL_iterate_mul (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] (x * y) =
      (AutomorphicForm.sigmaGL K L A σ)^[k] x * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaGL_iterate_inv (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] x⁻¹ = ((AutomorphicForm.sigmaGL K L A σ)^[k] x)⁻¹ := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_inv]

def pnorm (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (AutomorphicForm.sigmaGL K L A σ)^[i] y).prod

theorem pnorm_zero (y : GL (Fin 2) (L ⊗[K] A)) : pnorm K L A σ 0 y = 1 := by
  simp [pnorm]

theorem pnorm_succ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (k + 1) y = pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  simp [pnorm, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pnorm (y : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ y = pnorm K L A σ (Module.finrank K L) y := rfl

theorem pnorm_twistedConj (k : ℕ) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ k (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * pnorm K L A σ k δ * (AutomorphicForm.sigmaGL K L A σ)^[k] x := by
  induction k with
  | zero => simp [pnorm_zero]
  | succ k ih =>
      rw [pnorm_succ, ih, pnorm_succ, sigmaGL_iterate_mul, sigmaGL_iterate_mul, sigmaGL_iterate_inv,
        Function.iterate_succ_apply]
      group

def theta (δ : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) :=
  (MulAut.conj δ).toMonoidHom.comp (AutomorphicForm.sigmaGL K L A σ)

theorem theta_apply (δ g : GL (Fin 2) (L ⊗[K] A)) :
    theta K L A σ δ g = δ * AutomorphicForm.sigmaGL K L A σ g * δ⁻¹ := rfl

theorem twistedConj_eq (δ z : GL (Fin 2) (L ⊗[K] A)) :
    z⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ z = z⁻¹ * theta K L A σ δ z * δ := by
  rw [theta_apply]; group

theorem mem_twistedCentralizer_iff_theta (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔ theta K L A σ δ t = t := by
  rw [theta_apply]; exact AutomorphicForm.mem_sigmaCentralizer_iff_fixed

end Twist

section Order

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)

include hσ

theorem theta_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    theta K L A σ δ (AutomorphicForm.normString K L A σ δ) = AutomorphicForm.normString K L A σ δ := by
  have h := pnorm_twistedConj K L A σ (Module.finrank K L) δ δ
  rw [inv_mul_cancel, one_mul, sigmaGL_iterate_of_pow_eq_one K L A σ hσ, ← normString_eq_pnorm,
    ← normString_eq_pnorm] at h

  have hNσ : ∀ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)),
      pnorm K L A σ k (AutomorphicForm.sigmaGL K L A σ y) = AutomorphicForm.sigmaGL K L A σ (pnorm K L A σ k y) := by
    intro k y
    induction k with
    | zero => simp [pnorm_zero]
    | succ k ih =>
        rw [pnorm_succ, pnorm_succ, ih, map_mul, ← Function.iterate_succ_apply,
          Function.iterate_succ_apply']
  rw [normString_eq_pnorm, hNσ, ← normString_eq_pnorm] at h
  rw [theta_apply, h]; group

theorem theta_mem_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    theta K L A σ δ z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  have h := congrArg (theta K L A σ δ) hz
  rw [map_mul, map_mul, theta_normString K L A σ hσ] at h
  exact h

end Order

section CentralizerAlgebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (δ : GL (Fin 2) (L ⊗[K] A))

def sigmaM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (AutomorphicForm.sigmaTensor K L A σ).mapMatrix

theorem sigmaM_val (x : GL (Fin 2) (L ⊗[K] A)) :
    sigmaM K L A σ (x : Matrix (Fin 2) (Fin 2) _) = ((AutomorphicForm.sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := rfl

theorem sigmaM_smul_one (r : L ⊗[K] A) :
    sigmaM K L A σ (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
      (AutomorphicForm.sigmaTensor K L A σ r) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  ext i j
  simp only [sigmaM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs <;> simp

def thetaM : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A) where
  toFun X := δ.val * sigmaM K L A σ X * δ⁻¹.val
  map_one' := by rw [map_one, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' X Y := by
    rw [map_mul]
    have h : (δ⁻¹.val : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * δ.val = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc δ.val * (sigmaM K L A σ X * sigmaM K L A σ Y) * δ⁻¹.val
        = δ.val * sigmaM K L A σ X * (δ⁻¹.val * δ.val) * sigmaM K L A σ Y * δ⁻¹.val := by
          rw [h, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by rw [map_zero, mul_zero, zero_mul]
  map_add' X Y := by rw [map_add, mul_add, add_mul]

theorem thetaM_apply (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    thetaM K L A σ δ X = δ.val * sigmaM K L A σ X * δ⁻¹.val := rfl

theorem thetaM_val (x : GL (Fin 2) (L ⊗[K] A)) :
    thetaM K L A σ δ (x : Matrix (Fin 2) (Fin 2) _) = ((theta K L A σ δ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) := by
  rw [thetaM_apply, sigmaM_val, theta_apply, Units.val_mul, Units.val_mul]

theorem thetaM_smul_one (r : L ⊗[K] A) :
    thetaM K L A σ δ (r • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
      (AutomorphicForm.sigmaTensor K L A σ r) • (1 : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  rw [thetaM_apply, sigmaM_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one]

def E : Subalgebra (L ⊗[K] A) (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
  Subalgebra.centralizer (L ⊗[K] A)
    {((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))}

theorem mem_E_iff (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    X ∈ E K L A σ δ ↔
      X * ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) =
        ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _) * X := by
  rw [E, Subalgebra.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact eq_comm

theorem val_mem_E_iff (x : GL (Fin 2) (L ⊗[K] A)) :
    (x : Matrix (Fin 2) (Fin 2) _) ∈ E K L A σ δ ↔
      x ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [mem_E_iff, Subgroup.mem_centralizer_singleton_iff, ← Units.val_mul, ← Units.val_mul, Units.val_inj]

theorem E_isMulCommutative (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) :
    IsMulCommutative (E K L A σ δ) :=
  IsMulCommutative.of_comm fun X Y => Subtype.ext
    (mul_comm_of_commute _ _ _ ((mem_E_iff K L A σ δ _).1 X.2) ((mem_E_iff K L A σ δ _).1 Y.2) hδ)

theorem E_moduleFinite [IsArtinianRing A] : Module.Finite (L ⊗[K] A) (E K L A σ δ) := by
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI : IsNoetherian (L ⊗[K] A) (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective (E K L A σ δ).val.toLinearMap Subtype.val_injective

theorem E_isArtinianRing [IsArtinianRing A] : IsArtinianRing (E K L A σ δ) := by
  haveI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite A (L ⊗[K] A)
  haveI := E_moduleFinite K L A σ δ
  exact IsArtinianRing.of_finite (L ⊗[K] A) (E K L A σ δ)

theorem E_isReduced [IsReduced (L ⊗[K] A)]
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ)) :
    IsReduced (E K L A σ δ) := by
  refine (isReduced_iff_pow_one_lt 2 one_lt_two).2 fun X hX => ?_
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul _ _ ((mem_E_iff K L A σ δ _).1 X.2) hδ
  have h2 : (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 0 := by
    have := congrArg Subtype.val hX
    simpa [pow_two] using this
  rw [hab] at h2
  obtain ⟨ha, hb⟩ := eq_zero_of_sq_eq_zero _ hδ h2
  apply Subtype.ext
  rw [hab, ha, hb, zero_smul, zero_smul, add_zero]
  rfl

include hσ in

theorem thetaM_mem_E {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)} (hX : X ∈ E K L A σ δ) :
    thetaM K L A σ δ X ∈ E K L A σ δ := by
  rw [mem_E_iff] at hX ⊢
  have h := congrArg (thetaM K L A σ δ) hX
  rw [map_mul, map_mul, thetaM_val, theta_normString K L A σ hσ] at h
  exact h

include hσ in

def thetaE : E K L A σ δ →+* E K L A σ δ :=
  (thetaM K L A σ δ).restrict (E K L A σ δ) (E K L A σ δ) fun _ hX => thetaM_mem_E K L A σ hσ δ hX

theorem thetaE_val (X : E K L A σ δ) : ((thetaE K L A σ hσ δ X : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _) = thetaM K L A σ δ X := rfl

def unitOfE (z : GL (Fin 2) (L ⊗[K] A))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (E K L A σ δ)ˣ where
  val := ⟨(z : Matrix (Fin 2) (Fin 2) _), (val_mem_E_iff K L A σ δ z).2 hz⟩
  inv := ⟨((z⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) _), (val_mem_E_iff K L A σ δ z⁻¹).2 (Subgroup.inv_mem _ hz)⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

def ofUnitE : (E K L A σ δ)ˣ →* GL (Fin 2) (L ⊗[K] A) where
  toFun w :=
    { val := ((w : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _)
      inv := (((w⁻¹ : (E K L A σ δ)ˣ) : E K L A σ δ) : Matrix (Fin 2) (Fin 2) _)
      val_inv := by rw [← Subalgebra.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
      inv_val := by rw [← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel]; rfl }
  map_one' := Units.ext rfl
  map_mul' v w := Units.ext rfl

theorem ofUnitE_val (w : (E K L A σ δ)ˣ) :
    ((ofUnitE K L A σ δ w : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((w : E K L A σ δ) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := rfl

theorem ofUnitE_unitOfE (z : GL (Fin 2) (L ⊗[K] A))
    (hz : z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    ofUnitE K L A σ δ (unitOfE K L A σ δ z hz) = z := Units.ext rfl

theorem theta_ofUnitE (w : (E K L A σ δ)ˣ) :
    theta K L A σ δ (ofUnitE K L A σ δ w) = ofUnitE K L A σ δ (Units.map (thetaE K L A σ hσ δ).toMonoidHom w) := by
  apply Units.ext
  rw [← thetaM_val, ofUnitE_val, ofUnitE_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    thetaE_val]

end CentralizerAlgebra

section Factors

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))

abbrev F : Type := v.adicCompletion K

abbrev Rv : Type := L ⊗[K] v.adicCompletion K

abbrev EE : Type := E K L (v.adicCompletion K) σ δ

scoped instance instIsArtinianRingEE : IsArtinianRing (EE K L v σ δ) := E_isArtinianRing K L _ σ δ

scoped instance instIsReducedRv : IsReduced (Rv K L v) :=
  isReduced_of_injective (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective

def scalarE : F K v →+* EE K L v σ δ :=
  (algebraMap (Rv K L v) (EE K L v σ δ)).comp (algebraMap (F K v) (Rv K L v))

theorem scalarE_apply (c : F K v) :
    scalarE K L v σ δ c = algebraMap (Rv K L v) (EE K L v σ δ) (algebraMap (F K v) (Rv K L v) c) := rfl

theorem coe_scalarE (c : F K v) :
    ((scalarE K L v σ δ c : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) =
      (algebraMap (F K v) (Rv K L v) c) • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) := by
  rw [scalarE_apply, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]

theorem algebraMap_F_Rv (c : F K v) : algebraMap (F K v) (Rv K L v) c = (1 : L) ⊗ₜ[K] c := rfl

theorem rightSmul_eq (c : F K v) (x : Rv K L v) : c • x = ((1 : L) ⊗ₜ[K] c) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, mul_add, ha, hb]
  | tmul m t =>
      rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul,
        TensorProduct.comm_symm_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

scoped instance algFE : Algebra (F K v) (EE K L v σ δ) :=
  (scalarE K L v σ δ).toAlgebra' fun c x => Subtype.ext (by
    change (algebraMap (Rv K L v) (Matrix (Fin 2) (Fin 2) (Rv K L v)) (algebraMap (F K v) (Rv K L v) c)) *
        (x : Matrix (Fin 2) (Fin 2) (Rv K L v)) =
      (x : Matrix (Fin 2) (Fin 2) (Rv K L v)) * (algebraMap (Rv K L v) (Matrix (Fin 2) (Fin 2) (Rv K L v)) (algebraMap (F K v) (Rv K L v) c))
    exact Algebra.commutes _ _)

theorem algebraMap_FE (c : F K v) : algebraMap (F K v) (EE K L v σ δ) c = scalarE K L v σ δ c := rfl

theorem smul_EE_def (c : F K v) (y : EE K L v σ δ) : c • y = scalarE K L v σ δ c * y := rfl

scoped instance isScalarTower_F_Rv_EE : IsScalarTower (F K v) (Rv K L v) (EE K L v σ δ) :=
  ⟨fun c r y => Subtype.ext (by
    rw [smul_EE_def, Subalgebra.coe_smul, Subalgebra.coe_mul, Subalgebra.coe_smul, coe_scalarE, smul_one_mul', smul_smul',
      algebraMap_F_Rv, ← rightSmul_eq])⟩

scoped instance moduleFinite_F_EE : Module.Finite (F K v) (EE K L v σ δ) := by
  haveI := E_moduleFinite K L (v.adicCompletion K) σ δ
  exact Module.Finite.trans (Rv K L v) (EE K L v σ δ)

variable [IsMulCommutative (EE K L v σ δ)] [IsReduced (EE K L v σ δ)]

abbrev ι : Type := MaximalSpectrum (EE K L v σ δ)

scoped instance : Fintype (ι K L v σ δ) := Fintype.ofFinite _

abbrev πq (J : ι K L v σ δ) : EE K L v σ δ →+* EE K L v σ δ ⧸ J.asIdeal := Ideal.Quotient.mk J.asIdeal

scoped instance moduleFinite_quot (J : ι K L v σ δ) : Module.Finite (F K v) (EE K L v σ δ ⧸ J.asIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (F K v) J.asIdeal).toLinearMap Ideal.Quotient.mk_surjective

scoped instance isAlgebraic_quot (J : ι K L v σ δ) : Algebra.IsAlgebraic (F K v) (EE K L v σ δ ⧸ J.asIdeal) :=
  Algebra.IsAlgebraic.of_finite (F K v) _

theorem πq_eq_zero_iff (J : ι K L v σ δ) (x : EE K L v σ δ) : πq K L v σ δ J x = 0 ↔ x ∈ J.asIdeal :=
  Ideal.Quotient.eq_zero_iff_mem

theorem equivPi_apply (x : EE K L v σ δ) (J : ι K L v σ δ) :
    IsArtinianRing.equivPi (EE K L v σ δ) x J = πq K L v σ δ J x := rfl

theorem eq_of_forall_πq_eq {x y : EE K L v σ δ} (h : ∀ J : ι K L v σ δ, πq K L v σ δ J x = πq K L v σ δ J y) :
    x = y :=
  (IsArtinianRing.equivPi (EE K L v σ δ)).injective (funext fun J => by rw [equivPi_apply, equivPi_apply, h J])

theorem exists_forall_πq_eq (y : ∀ J : ι K L v σ δ, EE K L v σ δ ⧸ J.asIdeal) :
    ∃ x : EE K L v σ δ, ∀ J, πq K L v σ δ J x = y J :=
  ⟨(IsArtinianRing.equivPi (EE K L v σ δ)).symm y, fun J => by
    rw [← equivPi_apply, AlgEquiv.apply_symm_apply]⟩

theorem isUnit_iff_forall_πq_ne_zero (x : EE K L v σ δ) : IsUnit x ↔ ∀ J : ι K L v σ δ, πq K L v σ δ J x ≠ 0 := by
  constructor
  · intro hx J h
    exact (hx.map (πq K L v σ δ J)).ne_zero h
  · intro h
    by_contra hx
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
    exact h ⟨M, hM⟩ ((πq_eq_zero_iff K L v σ δ _ _).2 hxM)

def ν (J : ι K L v σ δ) (y : EE K L v σ δ) : ℝ :=
  spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) (πq K L v σ δ J y)

theorem ν_def (J : ι K L v σ δ) (y : EE K L v σ δ) :
    ν K L v σ δ J y = spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) (πq K L v σ δ J y) := rfl

theorem ν_mul (J : ι K L v σ δ) (y y' : EE K L v σ δ) : ν K L v σ δ J (y * y') = ν K L v σ δ J y * ν K L v σ δ J y' := by
  rw [ν_def, ν_def, ν_def, map_mul, map_mul]

theorem ν_one (J : ι K L v σ δ) : ν K L v σ δ J 1 = 1 := by rw [ν_def, map_one, map_one]

theorem ν_nonneg (J : ι K L v σ δ) (y : EE K L v σ δ) : 0 ≤ ν K L v σ δ J y := apply_nonneg _ _

theorem ν_eq_zero_iff (J : ι K L v σ δ) (y : EE K L v σ δ) : ν K L v σ δ J y = 0 ↔ πq K L v σ δ J y = 0 := by
  rw [ν_def, map_eq_zero_iff_eq_zero]

theorem ν_pos_iff (J : ι K L v σ δ) (y : EE K L v σ δ) : 0 < ν K L v σ δ J y ↔ πq K L v σ δ J y ≠ 0 := by
  rw [(ν_nonneg K L v σ δ J y).lt_iff_ne, ne_comm, Ne, ν_eq_zero_iff]

theorem ν_add_le (J : ι K L v σ δ) (y y' : EE K L v σ δ) :
    ν K L v σ δ J (y + y') ≤ max (ν K L v σ δ J y) (ν K L v σ δ J y') := by
  rw [ν_def, ν_def, ν_def, map_add]
  exact isNonarchimedean_spectralNorm _ _

theorem ν_pow (J : ι K L v σ δ) (y : EE K L v σ δ) (n : ℕ) : ν K L v σ δ J (y ^ n) = ν K L v σ δ J y ^ n := by
  rw [ν_def, ν_def, map_pow, map_pow]

theorem ν_scalarE (J : ι K L v σ δ) (c : F K v) : ν K L v σ δ J (scalarE K L v σ δ c) = ‖c‖ := by
  rw [ν_def]
  change spectralMulAlgNorm (F K v) _ (algebraMap (F K v) (EE K L v σ δ ⧸ J.asIdeal) c) = ‖c‖
  rw [spectralMulAlgNorm_def, spectralNorm_extends]

theorem ν_scalarE_mul (J : ι K L v σ δ) (c : F K v) (y : EE K L v σ δ) :
    ν K L v σ δ J (scalarE K L v σ δ c * y) = ‖c‖ * ν K L v σ δ J y := by
  rw [ν_mul, ν_scalarE]

theorem norm_le_one_of_aeval_int_eq_zero (J : ι K L v σ δ) {y : EE K L v σ δ ⧸ J.asIdeal} (p : Polynomial ℤ)
    (hp : p.Monic) (h : Polynomial.aeval y p = 0) :
    spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) y ≤ 1 := by
  set p' : Polynomial (F K v) := p.map (Int.castRingHom (F K v)) with hp'
  have hp'm : p'.Monic := hp.map _
  have h' : Polynomial.aeval y p' = 0 := by
    rw [Polynomial.aeval_def, hp', Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (F K v) (EE K L v σ δ ⧸ J.asIdeal)).comp (Int.castRingHom (F K v)))
        (algebraMap ℤ (EE K L v σ δ ⧸ J.asIdeal)), ← Polynomial.aeval_def, h]
  have h1 := norm_root_le_spectralValue (f := spectralAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal))
    spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm hp'm h'
  refine h1.trans ((spectralValue_le_one_iff hp'm).2 fun n => ?_)
  rw [hp', Polynomial.coeff_map, eq_intCast]
  exact IsUltrametricDist.norm_intCast_le_one (F K v) _

theorem norm_le_one_of_sq_eq (J : ι K L v σ δ) {x t d : EE K L v σ δ ⧸ J.asIdeal} (h : x * x = t * x - d)
    (ht : spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) t ≤ 1)
    (hd : spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) d ≤ 1) :
    spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) x ≤ 1 := by
  set f := spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) with hf
  by_contra hx
  push Not at hx
  have hx0 : 0 < f x := lt_trans zero_lt_one hx
  have h1 : f x * f x ≤ max (f t * f x) (f d) := by
    rw [← map_mul, h, sub_eq_add_neg]
    refine (isNonarchimedean_spectralNorm _ _).trans ?_
    rw [← spectralMulAlgNorm_def, ← spectralMulAlgNorm_def, ← hf, map_mul, map_neg_eq_map]
  rcases le_max_iff.1 h1 with h2 | h2
  · have : f x ≤ f t := le_of_mul_le_mul_right h2 hx0
    linarith
  · have h3 : (1 : ℝ) < f x * f x := by nlinarith
    linarith

variable {K L v σ δ}

def τOf (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α) (J : ι K L v σ δ) : ι K L v σ δ :=
  ⟨J.asIdeal.comap α, Ideal.comap_isMaximal_of_surjective α hα⟩

def barOf (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α) (J : ι K L v σ δ) :
    EE K L v σ δ ⧸ (τOf α hα J).asIdeal →+* EE K L v σ δ ⧸ J.asIdeal :=
  Ideal.quotientMap J.asIdeal α le_rfl

theorem barOf_mk (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α) (J : ι K L v σ δ) (x : EE K L v σ δ) :
    barOf α hα J (πq K L v σ δ (τOf α hα J) x) = πq K L v σ δ J (α x) := by
  rw [barOf, Ideal.quotientMap_mk]

def barAlgOf (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α)
    (hfix : ∀ c : F K v, α (scalarE K L v σ δ c) = scalarE K L v σ δ c) (J : ι K L v σ δ) :
    (EE K L v σ δ ⧸ (τOf α hα J).asIdeal) →ₐ[F K v] (EE K L v σ δ ⧸ J.asIdeal) :=
  { barOf α hα J with
    commutes' := fun c => by
      change barOf α hα J (πq K L v σ δ (τOf α hα J) (algebraMap (F K v) (EE K L v σ δ) c)) =
        πq K L v σ δ J (algebraMap (F K v) (EE K L v σ δ) c)
      rw [barOf_mk, algebraMap_FE, hfix] }

theorem ν_map_eq (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α)
    (hfix : ∀ c : F K v, α (scalarE K L v σ δ c) = scalarE K L v σ δ c) (J : ι K L v σ δ) (y : EE K L v σ δ) :
    ν K L v σ δ J (α y) = ν K L v σ δ (τOf α hα J) y := by
  rw [ν_def, ν_def, spectralMulAlgNorm_def, spectralMulAlgNorm_def, ← barOf_mk α hα J y]
  change spectralNorm (F K v) _ (barAlgOf α hα hfix J (πq K L v σ δ (τOf α hα J) y)) = _
  unfold spectralNorm
  rw [minpoly.algHom_eq (barAlgOf α hα hfix J) (RingHom.injective _)]

def cpow (c : F K v) (k : ι K L v σ δ → ℤ) : ∀ J : ι K L v σ δ, EE K L v σ δ ⧸ J.asIdeal :=
  fun J => (algebraMap (F K v) (EE K L v σ δ ⧸ J.asIdeal) c) ^ (k J)

theorem cpow_ne_zero {c : F K v} (hc : c ≠ 0) (k : ι K L v σ δ → ℤ) (J : ι K L v σ δ) : cpow c k J ≠ 0 :=
  zpow_ne_zero _ ((map_ne_zero (algebraMap (F K v) (EE K L v σ δ ⧸ J.asIdeal))).2 hc)

theorem norm_cpow (c : F K v) (k : ι K L v σ δ → ℤ) (J : ι K L v σ δ) :
    spectralMulAlgNorm (F K v) (EE K L v σ δ ⧸ J.asIdeal) (cpow c k J) = ‖c‖ ^ (k J) := by
  rw [cpow, map_zpow₀, spectralMulAlgNorm_def, spectralNorm_extends]

theorem barOf_cpow (α : EE K L v σ δ →+* EE K L v σ δ) (hα : Function.Surjective α)
    (hfix : ∀ c : F K v, α (scalarE K L v σ δ c) = scalarE K L v σ δ c) (c : F K v) (k : ι K L v σ δ → ℤ) (J : ι K L v σ δ)
    (hk : k (τOf α hα J) = k J) : barOf α hα J (cpow c k (τOf α hα J)) = cpow c k J := by
  change barAlgOf α hα hfix J _ = _
  rw [cpow, cpow, map_zpow₀, AlgHom.commutes, hk]

end Factors

section Integers

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def Osub : Subring (Rv K L v) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem mem_Osub_iff (x : Rv K L v) : x ∈ Osub K L v ↔ x ∈ AutomorphicForm.semiLocalIntegers K L v := by
  simp only [Osub, RingHom.mem_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AutomorphicForm.semiLocalIntegers,
    Set.mem_range]

theorem one_tmul_mem_Osub (x : v.adicCompletionIntegers K) : ((1 : L) ⊗ₜ[K] (x : F K v) : Rv K L v) ∈ Osub K L v :=
  ⟨(1 : 𝓞 L) ⊗ₜ x, by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]⟩

theorem sigmaTensor_mem_Osub (σ : L ≃ₐ[K] L) {x : Rv K L v} (hx : x ∈ Osub K L v) :
    AutomorphicForm.sigmaTensor K L (F K v) σ x ∈ Osub K L v := by
  obtain ⟨t, rfl⟩ := hx
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subring.zero_mem _
  | add a b ha hb => rw [map_add, map_add]; exact Subring.add_mem _ ha hb
  | tmul b x =>
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]
      have hσb : IsIntegral ℤ (σ (b : L)) := (RingOfIntegers.isIntegral_coe b).map σ
      refine ⟨(⟨σ (b : L), hσb⟩ : 𝓞 L) ⊗ₜ x, ?_⟩
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]
      simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (Rv K L v)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) (hh : h ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g * h ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet, ← mem_Osub_iff] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (Rv K L v)} (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g⁻¹ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem sigmaGL_mem_semiLocalIntegralSet (σ : L ≃ₐ[K] L) {g : GL (Fin 2) (Rv K L v)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    AutomorphicForm.sigmaGL K L (F K v) σ g ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet, ← mem_Osub_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sigmaGL_apply_val]; exact sigmaTensor_mem_Osub K L v σ (hg.1 i j)
  · rw [← map_inv, sigmaGL_apply_val]; exact sigmaTensor_mem_Osub K L v σ (hg.2 i j)

theorem normString_mem_semiLocalIntegralSet (σ : L ≃ₐ[K] L) {δ : GL (Fin 2) (Rv K L v)}
    (hδ : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    AutomorphicForm.normString K L (F K v) σ δ ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  have hit : ∀ i : ℕ, (AutomorphicForm.sigmaGL K L (F K v) σ)^[i] δ ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    intro i
    induction i with
    | zero => exact hδ
    | succ i ih => rw [Function.iterate_succ_apply']; exact sigmaGL_mem_semiLocalIntegralSet K L v σ ih
  rw [normString_eq_pnorm]
  induction (Module.finrank K L) with
  | zero => rw [pnorm_zero]; exact AutomorphicForm.one_mem_semiLocalIntegralSet K L v
  | succ k ih => rw [pnorm_succ]; exact mul_mem_semiLocalIntegralSet K L v ih (hit k)

variable (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))

def IsInt (y : EE K L v σ δ) : Prop := ∀ i j : Fin 2, (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) i j ∈ Osub K L v

theorem IsInt.mul {y y' : EE K L v σ δ} (hy : IsInt K L v σ δ y) (hy' : IsInt K L v σ δ y') : IsInt K L v σ δ (y * y') := by
  intro i j
  rw [Subalgebra.coe_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hy' k j)

theorem IsInt.pow {y : EE K L v σ δ} (hy : IsInt K L v σ δ y) (n : ℕ) : IsInt K L v σ δ (y ^ (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one]; exact hy
  | succ n ih => rw [pow_succ]; exact IsInt.mul K L v σ δ ih hy

theorem isInt_of_val_eq {y : EE K L v σ δ} {g : GL (Fin 2) (Rv K L v)} (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (h : (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) = g) : IsInt K L v σ δ y := fun i j => by
  rw [h, mem_Osub_iff]; exact hg.1 i j

theorem mul_self_eq (M : Matrix (Fin 2) (Fin 2) (Rv K L v)) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) := by
  refine matrix_eq_of_entries ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

variable [IsMulCommutative (EE K L v σ δ)] [IsReduced (EE K L v σ δ)]

theorem ν_algebraMap_le_one_of_mem (J : ι K L v σ δ) {r : Rv K L v} (hr : r ∈ Osub K L v) :
    ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) r) ≤ 1 := by
  obtain ⟨t, rfl⟩ := hr
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, ν_def, map_zero, map_zero]; exact zero_le_one
  | add a b ha hb => rw [map_add, map_add]; exact (ν_add_le K L v σ δ J _ _).trans (max_le ha hb)
  | tmul b x =>
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul]
      have hsplit : ((algebraMap (𝓞 L) L b) ⊗ₜ[K] (x : F K v) : Rv K L v) =
          ((b : L) ⊗ₜ[K] (1 : F K v)) * ((1 : L) ⊗ₜ[K] (x : F K v)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit, map_mul, ν_mul]
      refine mul_le_one₀ ?_ (ν_nonneg K L v σ δ J _) ?_
      ·
        set ψ : L →+* EE K L v σ δ ⧸ J.asIdeal :=
          (πq K L v σ δ J).comp ((algebraMap (Rv K L v) (EE K L v σ δ)).comp
            (Algebra.TensorProduct.includeLeftRingHom : L →+* Rv K L v)) with hψ
        have hz : πq K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) ((b : L) ⊗ₜ[K] (1 : F K v))) = ψ (b : L) := rfl
        rw [ν_def, hz]
        refine norm_le_one_of_aeval_int_eq_zero K L v σ δ J (minpoly ℤ (b : L)) (minpoly.monic (RingOfIntegers.isIntegral_coe b)) ?_
        have hb : ψ (b : L) = ψ.toIntAlgHom (b : L) := rfl
        rw [hb, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      ·
        have hsc : algebraMap (Rv K L v) (EE K L v σ δ) ((1 : L) ⊗ₜ[K] (x : F K v)) = scalarE K L v σ δ (x : F K v) := rfl
        rw [hsc, ν_scalarE, Valued.toNormedField.norm_le_one_iff]
        exact x.2

theorem ν_le_one_of_isInt (J : ι K L v σ δ) {y : EE K L v σ δ} (hy : IsInt K L v σ δ y) : ν K L v σ δ J y ≤ 1 := by
  set t : Rv K L v := Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) with ht
  set d : Rv K L v := Matrix.det (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) with hd
  have htO : t ∈ Osub K L v := by rw [ht, Matrix.trace_fin_two]; exact Subring.add_mem _ (hy 0 0) (hy 1 1)
  have hdO : d ∈ Osub K L v := by
    rw [hd, Matrix.det_fin_two]; exact Subring.sub_mem _ (Subring.mul_mem _ (hy 0 0) (hy 1 1)) (Subring.mul_mem _ (hy 0 1) (hy 1 0))
  have hCH : y * y = algebraMap (Rv K L v) (EE K L v σ δ) t * y - algebraMap (Rv K L v) (EE K L v σ δ) d := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul', mul_self_eq]
  rw [ν_def]
  refine norm_le_one_of_sq_eq K L v σ δ J (t := πq K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) t))
    (d := πq K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) d)) ?_ ?_ ?_
  · rw [← map_mul, hCH, map_sub (πq K L v σ δ J), map_mul (πq K L v σ δ J)]
  · exact ν_algebraMap_le_one_of_mem K L v σ δ J htO
  · exact ν_algebraMap_le_one_of_mem K L v σ δ J hdO

end Integers

section Closure

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))

abbrev ϖR (ϖ : K) : Rv K L v := (1 : L) ⊗ₜ[K] (ϖ : F K v)

theorem valued_ϖ {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) : Valued.v (ϖ : F K v) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]

theorem norm_ϖ_lt_one {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) : ‖(ϖ : F K v)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, valued_ϖ K v hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

theorem ϖ_ne_zero {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) : (ϖ : F K v) ≠ 0 := by
  intro h
  have := valued_ϖ K v hϖ
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem norm_ϖ_pos {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) : 0 < ‖(ϖ : F K v)‖ :=
  norm_pos_iff.2 (ϖ_ne_zero K v hϖ)

theorem ϖR_mem_Osub {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) : ϖR K L v ϖ ∈ Osub K L v := by
  have hle : Valued.v (ϖ : F K v) ≤ 1 := by
    rw [valued_ϖ K v hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  exact one_tmul_mem_Osub K L v ⟨(ϖ : F K v), hle⟩

theorem algebraMap_ϖR (ϖ : K) : algebraMap (Rv K L v) (EE K L v σ δ) (ϖR K L v ϖ) = scalarE K L v σ δ (ϖ : F K v) := rfl

theorem algebraMap_Rv_EE_injective : Function.Injective (algebraMap (Rv K L v) (EE K L v σ δ)) := by
  intro a b h
  have := congrArg (fun z : EE K L v σ δ => (z : Matrix (Fin 2) (Fin 2) (Rv K L v)) 0 0) h
  simpa [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one] using this

variable [IsMulCommutative (EE K L v σ δ)] [IsReduced (EE K L v σ δ)]

theorem mem_Osub_of_forall_ν_le_one
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) {s : Rv K L v}
    (h : ∀ J : ι K L v σ δ, ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) s) ≤ 1) : s ∈ Osub K L v := by
  by_contra hs
  rw [mem_Osub_iff] at hs
  obtain ⟨y, hy, e, -, he0, hee, hsye⟩ :=
    (AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
      K L v hv ϖ hϖ).2 s hs
  set eE := algebraMap (Rv K L v) (EE K L v σ δ) e with heE
  have heE0 : eE ≠ 0 := fun h0 => he0 (algebraMap_Rv_EE_injective K L v σ δ (by rw [← heE, h0, map_zero]))
  obtain ⟨J, hJ⟩ : ∃ J : ι K L v σ δ, πq K L v σ δ J eE ≠ 0 := by
    by_contra hall
    push Not at hall
    exact heE0 (eq_of_forall_πq_eq K L v σ δ fun J => by rw [hall J, map_zero])
  have h1 : πq K L v σ δ J eE = 1 := by
    have hid : πq K L v σ δ J eE * πq K L v σ δ J eE = πq K L v σ δ J eE := by
      rw [← map_mul, heE, ← map_mul, hee.eq]
    exact mul_left_cancel₀ hJ (by rw [hid, mul_one])
  have hν1 : ν K L v σ δ J eE = 1 := by rw [ν_def, h1, map_one]
  have hlt : ν K L v σ δ J eE < 1 := by
    rw [heE, ← hsye, map_mul, map_mul, ν_mul, ν_mul, algebraMap_ϖR, ν_scalarE]
    have h2 : ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) s) * ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) y) ≤ 1 :=
      mul_le_one₀ (h J) (ν_nonneg K L v σ δ J _) (ν_algebraMap_le_one_of_mem K L v σ δ J ((mem_Osub_iff K L v y).2 hy))
    have h3 : 0 ≤ ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) s) * ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) y) :=
      mul_nonneg (ν_nonneg K L v σ δ J _) (ν_nonneg K L v σ δ J _)
    calc ‖(ϖ : F K v)‖ * ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) s) *
          ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) y)
        = ‖(ϖ : F K v)‖ * (ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) s) *
          ν K L v σ δ J (algebraMap (Rv K L v) (EE K L v σ δ) y)) := by ring
      _ ≤ ‖(ϖ : F K v)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact norm_ϖ_lt_one K v hϖ
  linarith

def conjE : EE K L v σ δ →+* EE K L v σ δ where
  toFun y := ⟨conjM (y : Matrix (Fin 2) (Fin 2) (Rv K L v)), (mem_E_iff K L _ σ δ _).2
    (conjM_commute ((mem_E_iff K L _ σ δ _).1 y.2))⟩
  map_one' := Subtype.ext (by change conjM _ = _; rw [Subalgebra.coe_one, conjM_one])
  map_mul' y y' := Subtype.ext (by
    change conjM ((y * y' : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) = conjM (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * conjM y'
    rw [Subalgebra.coe_mul]
    exact conjM_mul_of_commute _ _ (congrArg Subtype.val (mul_comm y y')))
  map_zero' := Subtype.ext (by
    change conjM _ = _
    rw [Subalgebra.coe_zero, conjM, Matrix.trace_zero, sub_zero]
    exact zero_smul (Rv K L v) (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)))
  map_add' y y' := Subtype.ext (by
    change conjM ((y + y' : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) = conjM (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) + conjM y'
    rw [Subalgebra.coe_add, conjM_add])

theorem conjE_val (y : EE K L v σ δ) : ((conjE K L v σ δ y : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) = conjM y := rfl

theorem conjE_conjE (y : EE K L v σ δ) : conjE K L v σ δ (conjE K L v σ δ y) = y :=
  Subtype.ext (by rw [conjE_val, conjE_val, conjM_conjM])

theorem conjE_surjective : Function.Surjective (conjE K L v σ δ) := fun y => ⟨conjE K L v σ δ y, conjE_conjE K L v σ δ y⟩

theorem conjE_scalarE (c : F K v) : conjE K L v σ δ (scalarE K L v σ δ c) = scalarE K L v σ δ c :=
  Subtype.ext (by rw [conjE_val, coe_scalarE, conjM_smul_one])

theorem add_conjE (y : EE K L v σ δ) :
    y + conjE K L v σ δ y = algebraMap (Rv K L v) (EE K L v σ δ) (Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v))) :=
  Subtype.ext (by rw [Subalgebra.coe_add, conjE_val, add_conjM, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one])

theorem ν_conjE_le (J : ι K L v σ δ) {y : EE K L v σ δ} (h : ∀ J : ι K L v σ δ, ν K L v σ δ J y ≤ 1) :
    ν K L v σ δ J (conjE K L v σ δ y) ≤ 1 := by
  rw [ν_map_eq (conjE K L v σ δ) (conjE_surjective K L v σ δ) (conjE_scalarE K L v σ δ)]
  exact h _

theorem trace_mem_Osub_of_forall_ν_le_one
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ)) {y : EE K L v σ δ}
    (h : ∀ J : ι K L v σ δ, ν K L v σ δ J y ≤ 1) : Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) ∈ Osub K L v := by
  refine mem_Osub_of_forall_ν_le_one K L v σ δ hv hϖ fun J => ?_
  rw [← add_conjE]
  exact (ν_add_le K L v σ δ J _ _).trans (max_le (h J) (ν_conjE_le K L v σ δ J h))

def γE : EE K L v σ δ :=
  ⟨((AutomorphicForm.normString K L (F K v) σ δ : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v)),
    (val_mem_E_iff K L _ σ δ _).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)⟩

theorem γE_val : ((γE K L v σ δ : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) =
    ((AutomorphicForm.normString K L (F K v) σ δ : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v)) := rfl

structure IntData (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Prop where
  hδ : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v
  hdisc : ∃ u ∈ AutomorphicForm.semiLocalIntegers K L v,
      u * (Matrix.trace ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
            4 * Matrix.det ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1

abbrev gM : Matrix (Fin 2) (Fin 2) (Rv K L v) :=
  ((AutomorphicForm.normString K L (F K v) σ δ : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v))

variable {K L v σ δ} in
theorem IntData.g_mem (H : IntData K L v σ δ) (i j : Fin 2) : gM K L v σ δ i j ∈ Osub K L v := by
  rw [mem_Osub_iff]; exact (normString_mem_semiLocalIntegralSet K L v σ H.hδ).1 i j

variable {K L v σ δ} in
theorem IntData.trace_mem (H : IntData K L v σ δ) : (gM K L v σ δ).trace ∈ Osub K L v := by
  rw [Matrix.trace_fin_two]; exact Subring.add_mem _ (H.g_mem 0 0) (H.g_mem 1 1)

variable {K L v σ δ} in
theorem IntData.det_mem (H : IntData K L v σ δ) : (gM K L v σ δ).det ∈ Osub K L v := by
  rw [Matrix.det_fin_two]
  exact Subring.sub_mem _ (Subring.mul_mem _ (H.g_mem 0 0) (H.g_mem 1 1)) (Subring.mul_mem _ (H.g_mem 0 1) (H.g_mem 1 0))

variable {K L v σ δ} in
theorem IntData.isUnit_disc (H : IntData K L v σ δ) : IsUnit ((gM K L v σ δ).trace ^ 2 - 4 * (gM K L v σ δ).det) := by
  obtain ⟨u, -, hu⟩ := H.hdisc
  exact IsUnit.of_mul_eq_one_right u hu

variable {K L v σ δ} in
theorem IntData.γE_isInt (H : IntData K L v σ δ) : IsInt K L v σ δ (γE K L v σ δ) :=
  isInt_of_val_eq K L v σ δ (normString_mem_semiLocalIntegralSet K L v σ H.hδ) (γE_val K L v σ δ)

variable {K L v σ δ} in

theorem IntData.exists_int_decomp (H : IntData K L v σ δ) {y : EE K L v σ δ}
    (hp1 : Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) ∈ Osub K L v)
    (hp2 : Matrix.trace ((y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * gM K L v σ δ) ∈ Osub K L v) :
    ∃ a ∈ Osub K L v, ∃ b ∈ Osub K L v, (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) = a • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) + b • gM K L v σ δ := by
  obtain ⟨u, hu, hu1⟩ := H.hdisc
  have huO : u ∈ Osub K L v := (mem_Osub_iff K L v u).2 hu
  set g := gM K L v σ δ with hg
  set t : Rv K L v := g.trace with ht
  set d : Rv K L v := g.det with hd
  change u * (t ^ 2 - 4 * d) = 1 at hu1
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul g (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) ((mem_E_iff K L _ σ δ _).1 y.2) H.isUnit_disc
  obtain ⟨e00, e01, e10, e11⟩ := smul_one_add_smul_apply g a b
  rw [← hab] at e00 e01 e10 e11
  set p₁ := Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) with hp₁
  set p₂ := Matrix.trace ((y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * g) with hp₂
  have hp1e : p₁ = 2 * a + b * t := by
    rw [hp₁, Matrix.trace_fin_two, e00, e11, ht, Matrix.trace_fin_two]; ring
  have hp2e : p₂ = a * t + b * (t ^ 2 - 2 * d) := by
    rw [hp₂, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, e00, e01, e10, e11,
      ht, hd, Matrix.trace_fin_two, Matrix.det_fin_two]; ring
  have ha : a = u * ((t ^ 2 - 2 * d) * p₁ - t * p₂) := by rw [hp1e, hp2e]; linear_combination (-a) * hu1
  have hb : b = u * (2 * p₂ - t * p₁) := by rw [hp1e, hp2e]; linear_combination (-b) * hu1
  refine ⟨a, ?_, b, ?_, hab⟩
  · rw [ha]
    exact Subring.mul_mem _ huO (Subring.sub_mem _ (Subring.mul_mem _ (Subring.sub_mem _ (Subring.pow_mem _ H.trace_mem 2)
      (Subring.mul_mem _ (natCast_mem (Osub K L v) 2) H.det_mem)) hp1) (Subring.mul_mem _ H.trace_mem hp2))
  · rw [hb]
    exact Subring.mul_mem _ huO (Subring.sub_mem _ (Subring.mul_mem _ (natCast_mem (Osub K L v) 2) hp2)
      (Subring.mul_mem _ H.trace_mem hp1))

variable {K L v σ δ} in

theorem IntData.isInt_of_decomp (H : IntData K L v σ δ) {y : EE K L v σ δ} {a b : Rv K L v} (ha : a ∈ Osub K L v)
    (hb : b ∈ Osub K L v) (hab : (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) = a • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) + b • gM K L v σ δ) :
    IsInt K L v σ δ y := by
  obtain ⟨e00, e01, e10, e11⟩ := smul_one_add_smul_apply (gM K L v σ δ) a b
  rw [← hab] at e00 e01 e10 e11
  intro i j
  fin_cases i <;> fin_cases j
  · change (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) 0 0 ∈ _; rw [e00]; exact Subring.add_mem _ ha (Subring.mul_mem _ hb (H.g_mem 0 0))
  · change (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) 0 1 ∈ _; rw [e01]; exact Subring.mul_mem _ hb (H.g_mem 0 1)
  · change (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) 1 0 ∈ _; rw [e10]; exact Subring.mul_mem _ hb (H.g_mem 1 0)
  · change (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) 1 1 ∈ _; rw [e11]; exact Subring.add_mem _ ha (Subring.mul_mem _ hb (H.g_mem 1 1))

def ofCoords (a b : Rv K L v) : EE K L v σ δ :=
  ⟨a • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) + b • gM K L v σ δ, (mem_E_iff K L _ σ δ _).2 (smul_one_add_smul_commute _ a b)⟩

theorem ofCoords_val (a b : Rv K L v) :
    ((ofCoords K L v σ δ a b : EE K L v σ δ) : Matrix (Fin 2) (Fin 2) (Rv K L v)) = a • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) + b • gM K L v σ δ := rfl

variable {K L v σ δ}

theorem isInt_of_forall_ν_le_one (H : IntData K L v σ δ)
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    {y : EE K L v σ δ} (h : ∀ J : ι K L v σ δ, ν K L v σ δ J y ≤ 1) : IsInt K L v σ δ y := by
  have hp1 : Matrix.trace (y : Matrix (Fin 2) (Fin 2) (Rv K L v)) ∈ Osub K L v :=
    trace_mem_Osub_of_forall_ν_le_one K L v σ δ hv hϖ h
  have h' : ∀ J : ι K L v σ δ, ν K L v σ δ J (y * γE K L v σ δ) ≤ 1 := fun J => by
    rw [ν_mul]; exact mul_le_one₀ (h J) (ν_nonneg K L v σ δ J _) (ν_le_one_of_isInt K L v σ δ J H.γE_isInt)
  have hp2 : Matrix.trace ((y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * gM K L v σ δ) ∈ Osub K L v :=
    trace_mem_Osub_of_forall_ν_le_one K L v σ δ hv hϖ h'
  obtain ⟨a, ha, b, hb, hab⟩ := H.exists_int_decomp hp1 hp2
  exact H.isInt_of_decomp ha hb hab

theorem exists_eq_scalarE_mul_of_mul_self (H : IntData K L v σ δ)
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    {y y₁ : EE K L v σ δ} (hy : IsInt K L v σ δ y) (hy₁ : IsInt K L v σ δ y₁)
    (h : y * y = scalarE K L v σ δ (ϖ : F K v) * y₁) :
    ∃ y₂ : EE K L v σ δ, IsInt K L v σ δ y₂ ∧ y = scalarE K L v σ δ (ϖ : F K v) * y₂ := by
  have hU := (AutomorphicForm.exists_eq_tmul_mul_of_mul_self_eq_and_exists_isIdempotentElem_of_not_mem_semiLocalIntegers
    K L v hv ϖ hϖ).1
  obtain ⟨u, hu, hu1⟩ := H.hdisc
  have huO : u ∈ Osub K L v := (mem_Osub_iff K L v u).2 hu
  change u * ((gM K L v σ δ).trace ^ 2 - 4 * (gM K L v σ δ).det) = 1 at hu1

  have htr : ∀ {z : EE K L v σ δ}, IsInt K L v σ δ z → Matrix.trace (z : Matrix (Fin 2) (Fin 2) (Rv K L v)) ∈ Osub K L v :=
    fun hz => by rw [Matrix.trace_fin_two]; exact Subring.add_mem _ (hz 0 0) (hz 1 1)
  obtain ⟨a, haO, b, hbO, hab⟩ := H.exists_int_decomp (htr hy) (htr (IsInt.mul K L v σ δ hy H.γE_isInt))
  obtain ⟨a₁, ha₁O, b₁, hb₁O, hab₁⟩ := H.exists_int_decomp (htr hy₁) (htr (IsInt.mul K L v σ δ hy₁ H.γE_isInt))

  have hval := congrArg Subtype.val h
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hab, hab₁, coe_scalarE, smul_one_mul', smul_one_add_smul_mul_self,
    algebraMap_F_Rv, smul_smul_one_add_smul] at hval
  have hzero : (a * a - b * b * (gM K L v σ δ).det - ϖR K L v ϖ * a₁) • (1 : Matrix (Fin 2) (Fin 2) (Rv K L v)) +
      (2 * a * b + b * b * (gM K L v σ δ).trace - ϖR K L v ϖ * b₁) • gM K L v σ δ = 0 := by
    rw [sub_smul (a * a - b * b * (gM K L v σ δ).det) (ϖR K L v ϖ * a₁),
      sub_smul (2 * a * b + b * b * (gM K L v σ δ).trace) (ϖR K L v ϖ * b₁), ← sub_eq_zero.2 hval]
    abel
  obtain ⟨E1, E2⟩ := eq_zero_of_smul_one_add_smul_eq_zero (gM K L v σ δ) H.isUnit_disc hzero

  have hb3 : b ^ 3 * ((gM K L v σ δ).trace ^ 2 - 4 * (gM K L v σ δ).det) =
      ϖR K L v ϖ * ((b * (gM K L v σ δ).trace - 2 * a) * b₁ + 4 * a₁ * b) := by
    linear_combination (b * (gM K L v σ δ).trace - 2 * a) * E2 + (4 * b) * E1
  have hb3' : b ^ 3 = ϖR K L v ϖ * (u * ((b * (gM K L v σ δ).trace - 2 * a) * b₁ + 4 * a₁ * b)) := by
    linear_combination (-(b ^ 3)) * hu1 + u * hb3
  have hcO : u * ((b * (gM K L v σ δ).trace - 2 * a) * b₁ + 4 * a₁ * b) ∈ Osub K L v :=
    Subring.mul_mem _ huO (Subring.add_mem _ (Subring.mul_mem _ (Subring.sub_mem _ (Subring.mul_mem _ hbO H.trace_mem)
      (Subring.mul_mem _ (natCast_mem (Osub K L v) 2) haO)) hb₁O)
      (Subring.mul_mem _ (Subring.mul_mem _ (natCast_mem (Osub K L v) 4) ha₁O) hbO))
  have hpO : ϖR K L v ϖ ∈ Osub K L v := ϖR_mem_Osub K L v hϖ
  obtain ⟨z, hz, hbz⟩ := hU (b * b) ((mem_Osub_iff K L v _).1 (Subring.mul_mem _ hbO hbO))
    (b * (u * ((b * (gM K L v σ δ).trace - 2 * a) * b₁ + 4 * a₁ * b))) ((mem_Osub_iff K L v _).1 (Subring.mul_mem _ hbO hcO))
    (by linear_combination b * hb3')
  obtain ⟨b', hb', hbb'⟩ := hU b ((mem_Osub_iff K L v _).1 hbO) z hz hbz
  have hb'O : b' ∈ Osub K L v := (mem_Osub_iff K L v _).2 hb'
  obtain ⟨a', ha', haa'⟩ := hU a ((mem_Osub_iff K L v _).1 haO) (ϖR K L v ϖ * (b' * b') * (gM K L v σ δ).det + a₁)
    ((mem_Osub_iff K L v _).1 (Subring.add_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hpO (Subring.mul_mem _ hb'O hb'O))
      H.det_mem) ha₁O))
    (by rw [hbb'] at E1; linear_combination E1)
  have ha'O : a' ∈ Osub K L v := (mem_Osub_iff K L v _).2 ha'
  refine ⟨ofCoords K L v σ δ a' b', H.isInt_of_decomp ha'O hb'O (ofCoords_val K L v σ δ a' b'), Subtype.ext ?_⟩
  rw [hab, Subalgebra.coe_mul, coe_scalarE, ofCoords_val, smul_one_mul', algebraMap_F_Rv, smul_smul_one_add_smul, ← haa',
    ← hbb']

theorem exists_eq_scalarE_mul_of_pow (H : IntData K L v σ δ)
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    {y : EE K L v σ δ} (hy : IsInt K L v σ δ y) (n : ℕ)
    (h : ∃ y₁ : EE K L v σ δ, IsInt K L v σ δ y₁ ∧ y ^ (n + 1) = scalarE K L v σ δ (ϖ : F K v) * y₁) :
    ∃ y₂ : EE K L v σ δ, IsInt K L v σ δ y₂ ∧ y = scalarE K L v σ δ (ϖ : F K v) * y₂ := by

  have h2 : ∀ (s : ℕ) (z : EE K L v σ δ), IsInt K L v σ δ z →
      (∃ y₁ : EE K L v σ δ, IsInt K L v σ δ y₁ ∧ z ^ (2 ^ s) = scalarE K L v σ δ (ϖ : F K v) * y₁) →
      ∃ y₂ : EE K L v σ δ, IsInt K L v σ δ y₂ ∧ z = scalarE K L v σ δ (ϖ : F K v) * y₂ := by
    intro s
    induction s with
    | zero => intro z hz hz1; simpa only [pow_zero, pow_one] using hz1
    | succ s ih =>
        intro z hz ⟨y₁, hy₁, hzy⟩
        have hzs : IsInt K L v σ δ (z ^ (2 ^ s)) := by
          obtain ⟨m, hm⟩ : ∃ m, 2 ^ s = m + 1 := ⟨2 ^ s - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
          rw [hm]; exact IsInt.pow K L v σ δ hz m
        obtain ⟨y₂, hy₂, hz2⟩ := exists_eq_scalarE_mul_of_mul_self H hv hϖ hzs hy₁ (by rw [← pow_two, ← pow_mul, ← pow_succ, hzy])
        exact ih z hz ⟨y₂, hy₂, hz2⟩

  obtain ⟨y₁, hy₁, hy1⟩ := h
  refine h2 (n + 1) y hy ⟨y ^ (2 ^ (n + 1) - (n + 1) - 1 + 1) * y₁, IsInt.mul K L v σ δ (IsInt.pow K L v σ δ hy _) hy₁, ?_⟩
  have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hexp : 2 ^ (n + 1) = (2 ^ (n + 1) - (n + 1) - 1 + 1) + (n + 1) := by omega
  rw [mul_left_comm, ← hy1, ← pow_add, ← hexp]

theorem exists_idempotent (J : ι K L v σ δ) :
    ∃ e : EE K L v σ δ, πq K L v σ δ J e = 1 ∧ ∀ J', J' ≠ J → πq K L v σ δ J' e = 0 := by
  classical
  obtain ⟨e, he⟩ := exists_forall_πq_eq K L v σ δ (fun J' => if J' = J then 1 else 0)
  exact ⟨e, by rw [he]; simp, fun J' hJ' => by rw [he]; simp [hJ']⟩

theorem exists_ν_eq_zpow (H : IntData K L v σ δ)
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1 : ℤ))
    (J : ι K L v σ δ) {y : EE K L v σ δ} (hy : πq K L v σ δ J y ≠ 0) :
    ∃ k : ℤ, ν K L v σ δ J y = ‖(ϖ : F K v)‖ ^ k := by
  set r : ℝ := ‖(ϖ : F K v)‖ with hr
  have hr0 : 0 < r := norm_ϖ_pos K v hϖ
  have hr1 : r < 1 := norm_ϖ_lt_one K v hϖ
  have hϖ0 : (ϖ : F K v) ≠ 0 := ϖ_ne_zero K v hϖ
  have hn : 0 < ν K L v σ δ J y := (ν_pos_iff K L v σ δ J y).2 hy
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ioc_zpow hn ((one_lt_inv₀ hr0).2 hr1)
  rw [inv_zpow'] at hm1 hm2
  set k : ℤ := -(m + 1) with hk

  set y' : EE K L v σ δ := scalarE K L v σ δ ((ϖ : F K v) ^ (-k)) * y with hy'
  have hνy' : ν K L v σ δ J y' = r ^ (-k) * ν K L v σ δ J y := by rw [hy', ν_scalarE_mul, norm_zpow]
  have hy'1 : ν K L v σ δ J y' ≤ 1 := by
    rw [hνy']
    calc r ^ (-k) * ν K L v σ δ J y ≤ r ^ (-k) * r ^ (-(m + 1)) := mul_le_mul_of_nonneg_left hm2 (zpow_nonneg hr0.le _)
      _ = 1 := by rw [← zpow_add₀ hr0.ne', hk]; simp
  have hy'r : r < ν K L v σ δ J y' := by
    rw [hνy']
    calc r = r ^ (-k) * r ^ (-m) := by rw [← zpow_add₀ hr0.ne', hk]; ring_nf; simp
      _ < r ^ (-k) * ν K L v σ δ J y := mul_lt_mul_of_pos_left hm1 (zpow_pos hr0 _)
  rcases hy'1.lt_or_eq with hlt | heq
  ·
    exfalso
    obtain ⟨e, he1, he0⟩ := exists_idempotent J
    set z : EE K L v σ δ := e * y' with hz
    have hzJ : ν K L v σ δ J z = ν K L v σ δ J y' := by rw [ν_def, hz, map_mul, he1, one_mul, ← ν_def]
    have hzJ' : ∀ J', J' ≠ J → ν K L v σ δ J' z = 0 := fun J' hJ' => by
      rw [ν_eq_zero_iff, hz, map_mul, he0 J' hJ', zero_mul]
    have hzle : ∀ J', ν K L v σ δ J' z ≤ 1 := fun J' => by
      by_cases hJ' : J' = J
      · rw [hJ', hzJ]; exact hy'1
      · rw [hzJ' J' hJ']; exact zero_le_one
    have hzint : IsInt K L v σ δ z := isInt_of_forall_ν_le_one H hv hϖ hzle
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hr0 hlt
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
      rcases N with _ | N'
      · rw [pow_zero] at hN; exact absurd hN (not_lt.2 hr1.le)
      · exact ⟨N', rfl⟩

    set w' : EE K L v σ δ := scalarE K L v σ δ ((ϖ : F K v)⁻¹) * z ^ (N' + 1) with hw'
    have hw'le : ∀ J', ν K L v σ δ J' w' ≤ 1 := fun J' => by
      rw [hw', ν_scalarE_mul, norm_inv, ν_pow]
      by_cases hJ' : J' = J
      · rw [hJ', hzJ]
        calc r⁻¹ * ν K L v σ δ J y' ^ (N' + 1) ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hN.le (inv_nonneg.2 hr0.le)
          _ = 1 := inv_mul_cancel₀ hr0.ne'
      · rw [hzJ' J' hJ', zero_pow (Nat.succ_ne_zero N'), mul_zero]; exact zero_le_one
    have hw'int : IsInt K L v σ δ w' := isInt_of_forall_ν_le_one H hv hϖ hw'le
    have hzpow : z ^ (N' + 1) = scalarE K L v σ δ (ϖ : F K v) * w' := by
      rw [hw', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, one_mul]
    obtain ⟨y₂, hy₂, hzy₂⟩ := exists_eq_scalarE_mul_of_pow H hv hϖ hzint N' ⟨w', hw'int, hzpow⟩
    have : ν K L v σ δ J z ≤ r := by
      rw [hzy₂, ν_scalarE_mul]
      calc r * ν K L v σ δ J y₂ ≤ r * 1 := mul_le_mul_of_nonneg_left (ν_le_one_of_isInt K L v σ δ J hy₂) hr0.le
        _ = r := mul_one r
    rw [hzJ] at this
    exact absurd (this.trans_lt hy'r) (lt_irrefl _)
  · refine ⟨k, ?_⟩
    have h1 : r ^ (-k) * ν K L v σ δ J y = 1 := by rw [← hνy', heq]
    calc ν K L v σ δ J y = r ^ k * (r ^ (-k) * ν K L v σ δ J y) := by
          rw [← mul_assoc, ← zpow_add₀ hr0.ne', add_neg_cancel, zpow_zero, one_mul]
      _ = r ^ k := by rw [h1, mul_one]

end Closure

section Theta

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))

theorem sigmaTensor_symm_apply (x : Rv K L v) :
    AutomorphicForm.sigmaTensor K L (F K v) σ.symm (AutomorphicForm.sigmaTensor K L (F K v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul l c => simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem conj_cancel (M : Matrix (Fin 2) (Fin 2) (Rv K L v)) : δ⁻¹.val * (δ.val * M * δ⁻¹.val) * δ.val = M := by
  rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]

include hσ

theorem thetaE_scalarE (c : F K v) : thetaE K L (F K v) σ hσ δ (scalarE K L v σ δ c) = scalarE K L v σ δ c := by
  apply Subtype.ext
  rw [thetaE_val, coe_scalarE, thetaM_smul_one, algebraMap_F_Rv]
  congr 1
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

omit hσ in
theorem sigmaTensor_apply_symm (x : Rv K L v) :
    AutomorphicForm.sigmaTensor K L (F K v) σ (AutomorphicForm.sigmaTensor K L (F K v) σ.symm x) = x := by
  have h := sigmaTensor_symm_apply K L v σ.symm x
  rwa [AlgEquiv.symm_symm] at h

omit hσ in
theorem conj_cancel' (M : Matrix (Fin 2) (Fin 2) (Rv K L v)) : δ.val * (δ⁻¹.val * M * δ.val) * δ⁻¹.val = M := by
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

omit hσ in
theorem thetaM_injective : Function.Injective (thetaM K L (F K v) σ δ) := by
  intro X Y h
  rw [thetaM_apply, thetaM_apply] at h
  have h2 : sigmaM K L (F K v) σ X = sigmaM K L (F K v) σ Y := by
    rw [← conj_cancel K L v δ (sigmaM K L (F K v) σ X), h, conj_cancel]
  ext i j
  have hij := congr_fun (congr_fun h2 i) j
  simp only [sigmaM, RingHom.mapMatrix_apply, Matrix.map_apply] at hij
  rw [← sigmaTensor_symm_apply K L v σ (X i j), hij, sigmaTensor_symm_apply]

theorem thetaE_surjective : Function.Surjective (thetaE K L (F K v) σ hσ δ) := by
  intro Y
  set X : Matrix (Fin 2) (Fin 2) (Rv K L v) :=
    (AutomorphicForm.sigmaTensor K L (F K v) σ.symm).mapMatrix (δ⁻¹.val * (Y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * δ.val) with hXd
  have hX : thetaM K L (F K v) σ δ X = (Y : Matrix (Fin 2) (Fin 2) (Rv K L v)) := by
    have hs : sigmaM K L (F K v) σ X = δ⁻¹.val * (Y : Matrix (Fin 2) (Fin 2) (Rv K L v)) * δ.val := by
      ext i j
      simp only [sigmaM, hXd, RingHom.mapMatrix_apply, Matrix.map_apply, sigmaTensor_apply_symm]
    rw [thetaM_apply, hs, conj_cancel']
  have hγ : thetaM K L (F K v) σ δ ((AutomorphicForm.normString K L (F K v) σ δ : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v)) =
      ((AutomorphicForm.normString K L (F K v) σ δ : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v)) := by
    rw [thetaM_val, theta_normString K L (F K v) σ hσ δ]
  have hXE : X ∈ E K L (F K v) σ δ := by
    rw [mem_E_iff]
    apply thetaM_injective K L v σ δ
    rw [map_mul, map_mul, hX, hγ]
    exact (mem_E_iff K L (F K v) σ δ _).1 Y.2
  exact ⟨⟨X, hXE⟩, Subtype.ext (by rw [thetaE_val]; exact hX)⟩

end Theta

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (hσ : σ ^ Module.finrank K L = 1)
  {δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}

theorem le_one_mul_eq_one {a b : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  by_contra hne
  exact absurd h (mul_lt_one_of_nonneg_of_lt_one_left ha0 (lt_of_le_of_ne ha hne) hb).ne

include hσ in
theorem main
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hδO : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (hdisc : ∃ u ∈ AutomorphicForm.semiLocalIntegers K L v,
      u * (Matrix.trace ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
            4 * Matrix.det ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1) :
    {z : GL (Fin 2) (Rv K L v) |
        z ∈ Subgroup.centralizer ({AutomorphicForm.normString K L (F K v) σ δ} : Set (GL (Fin 2) (Rv K L v))) ∧
          z⁻¹ * δ * AutomorphicForm.sigmaGL K L (F K v) σ z ∈ AutomorphicForm.semiLocalIntegralSet K L v} ⊆
      (AutomorphicForm.twistedCentralizer K L (F K v) σ δ : Set (GL (Fin 2) (Rv K L v))) *
        AutomorphicForm.semiLocalIntegralSet K L v := by
  classical
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  have hunit : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (F K v) σ δ) := by
    obtain ⟨u, -, hu⟩ := hdisc
    exact IsUnit.of_mul_eq_one_right u hu
  haveI : IsMulCommutative (EE K L v σ δ) := E_isMulCommutative K L (F K v) σ δ hunit
  haveI : IsReduced (EE K L v σ δ) := E_isReduced K L (F K v) σ δ hunit
  have H : IntData K L v σ δ := ⟨hδO, hdisc⟩
  set r : ℝ := ‖(ϖ : F K v)‖ with hr
  have hr0 : 0 < r := norm_ϖ_pos K v hϖ
  have hr1 : r < 1 := norm_ϖ_lt_one K v hϖ
  have hϖ0 : (ϖ : F K v) ≠ 0 := ϖ_ne_zero K v hϖ
  set θE' := thetaE K L (F K v) σ hσ δ with hθE'
  have hsurj := thetaE_surjective K L v σ hσ δ
  have hfix := thetaE_scalarE K L v σ hσ δ
  rintro z ⟨hzZ, hzO⟩

  have hcZ : z⁻¹ * theta K L (F K v) σ δ z ∈
      Subgroup.centralizer ({AutomorphicForm.normString K L (F K v) σ δ} : Set (GL (Fin 2) (Rv K L v))) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hzZ) (theta_mem_centralizer K L (F K v) σ hσ δ hzZ)
  have hcO : z⁻¹ * theta K L (F K v) σ δ z ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    have : z⁻¹ * theta K L (F K v) σ δ z = z⁻¹ * δ * AutomorphicForm.sigmaGL K L (F K v) σ z * δ⁻¹ := by
      rw [twistedConj_eq]; group
    rw [this]; exact mul_mem_semiLocalIntegralSet K L v hzO (inv_mem_semiLocalIntegralSet K L v hδO)
  set zu : (EE K L v σ δ)ˣ := unitOfE K L (F K v) σ δ z hzZ with hzu
  set cu : (EE K L v σ δ)ˣ := unitOfE K L (F K v) σ δ _ hcZ with hcu
  have hθzu : θE' (zu : EE K L v σ δ) = (zu : EE K L v σ δ) * cu := by
    apply Subtype.ext
    rw [hθE', thetaE_val, Subalgebra.coe_mul]
    change thetaM K L (F K v) σ δ (z : Matrix (Fin 2) (Fin 2) (Rv K L v)) =
      (z : Matrix (Fin 2) (Fin 2) (Rv K L v)) * ((z⁻¹ * theta K L (F K v) σ δ z : GL (Fin 2) (Rv K L v)) : Matrix (Fin 2) (Fin 2) (Rv K L v))
    rw [thetaM_val, Units.val_mul, Units.mul_inv_cancel_left]

  have hcuint : IsInt K L v σ δ (cu : EE K L v σ δ) := isInt_of_val_eq K L v σ δ hcO rfl
  have hcuinv : IsInt K L v σ δ ((cu⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) :=
    isInt_of_val_eq K L v σ δ (inv_mem_semiLocalIntegralSet K L v hcO) rfl
  have hνc : ∀ J : ι K L v σ δ, ν K L v σ δ J (cu : EE K L v σ δ) = 1 := fun J =>
    le_one_mul_eq_one (ν_nonneg K L v σ δ J _) (ν_le_one_of_isInt K L v σ δ J hcuint) (ν_le_one_of_isInt K L v σ δ J hcuinv)
      (by rw [← ν_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ν_one])

  have hzu0 : ∀ J : ι K L v σ δ, πq K L v σ δ J (zu : EE K L v σ δ) ≠ 0 :=
    (isUnit_iff_forall_πq_ne_zero K L v σ δ _).1 (Units.isUnit zu)
  choose k hk using fun J => exists_ν_eq_zpow H hv hϖ J (hzu0 J)
  have hkτ : ∀ J : ι K L v σ δ, k (τOf θE' hsurj J) = k J := fun J => by
    apply zpow_right_injective₀ hr0 hr1.ne
    change r ^ k (τOf θE' hsurj J) = r ^ k J
    rw [← hk, ← hk, ← ν_map_eq θE' hsurj hfix J, hθzu, ν_mul, hνc, mul_one]

  obtain ⟨t, ht⟩ := exists_forall_πq_eq K L v σ δ (cpow (ϖ : F K v) k)
  have ht0 : ∀ J : ι K L v σ δ, πq K L v σ δ J t ≠ 0 := fun J => by
    rw [ht]; exact cpow_ne_zero hϖ0 k J
  set tu : (EE K L v σ δ)ˣ := ((isUnit_iff_forall_πq_ne_zero K L v σ δ t).2 ht0).unit with htu
  have htuval : (tu : EE K L v σ δ) = t := rfl
  have hθt : θE' t = t := by
    refine eq_of_forall_πq_eq K L v σ δ fun J => ?_
    rw [← barOf_mk θE' hsurj J, ht, ht, barOf_cpow θE' hsurj hfix _ k J (hkτ J)]
  have hνt : ∀ J : ι K L v σ δ, ν K L v σ δ J t = r ^ k J := fun J => by
    rw [ν_def, ht, norm_cpow]
  have hνtinv : ∀ J : ι K L v σ δ, ν K L v σ δ J ((tu⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) = r ^ (-k J) := fun J => by
    have h1 : ν K L v σ δ J ((tu⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) * ν K L v σ δ J t = 1 := by
      rw [← htuval, ← ν_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ν_one]
    rw [hνt] at h1
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h1

  set tG : GL (Fin 2) (Rv K L v) := ofUnitE K L (F K v) σ δ tu with htG
  have htG' : tG ∈ AutomorphicForm.twistedCentralizer K L (F K v) σ δ := by
    rw [mem_twistedCentralizer_iff_theta, htG, theta_ofUnitE K L (F K v) σ hσ δ]
    congr 1
    exact Units.ext hθt

  set du : (EE K L v σ δ)ˣ := tu⁻¹ * zu with hdu
  have hd : tG⁻¹ * z = ofUnitE K L (F K v) σ δ du := by
    rw [hdu, map_mul, map_inv, htG, hzu, ofUnitE_unitOfE]
  have hνd : ∀ J : ι K L v σ δ, ν K L v σ δ J (du : EE K L v σ δ) = 1 := fun J => by
    rw [hdu, Units.val_mul, ν_mul, hνtinv, hk, ← zpow_add₀ hr0.ne', neg_add_cancel, zpow_zero]
  have hνdinv : ∀ J : ι K L v σ δ, ν K L v σ δ J ((du⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) = 1 := fun J => by
    rw [hdu, mul_inv_rev, inv_inv, Units.val_mul, ν_mul, htuval, hνt]
    have h1 : ν K L v σ δ J ((zu⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) * ν K L v σ δ J (zu : EE K L v σ δ) = 1 := by
      rw [← ν_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ν_one]
    rw [hk] at h1
    rw [eq_inv_of_mul_eq_one_left h1, ← zpow_neg, ← zpow_add₀ hr0.ne', neg_add_cancel, zpow_zero]
  have hdint : IsInt K L v σ δ (du : EE K L v σ δ) := isInt_of_forall_ν_le_one H hv hϖ fun J => (hνd J).le
  have hdinvint : IsInt K L v σ δ ((du⁻¹ : (EE K L v σ δ)ˣ) : EE K L v σ δ) :=
    isInt_of_forall_ν_le_one H hv hϖ fun J => (hνdinv J).le
  have hdO : tG⁻¹ * z ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    rw [hd]
    simp only [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet, ← mem_Osub_iff]
    exact ⟨fun i j => hdint i j, fun i j => hdinvint i j⟩
  refine ⟨tG, htG', tG⁻¹ * z, hdO, ?_⟩
  change tG * (tG⁻¹ * z) = z
  rw [mul_inv_cancel_left]

end Main

end P2mTwistedTorusUnram
p2m_reactivate "P2MW.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one.P2mTwistedTorusUnram"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one.P2mTwistedTorusUnram"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (hdisc : ∃ u ∈ AutomorphicForm.semiLocalIntegers K L v,
      u * (Matrix.trace ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
            4 * Matrix.det ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1) :
    {z : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        z ∈ Subgroup.centralizer
            ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} :
              Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧
          z⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z ∈
            AutomorphicForm.semiLocalIntegralSet K L v} ⊆
      (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * AutomorphicForm.semiLocalIntegralSet K L v :=
  P2mTwistedTorusUnram.main hσ hv hδ hdisc

end S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one (solution)
