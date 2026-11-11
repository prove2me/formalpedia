-- Prove2me | Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
-- name    : QEC_Distillation_Universality_OneQubitClifford
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:14:52.016497+00:00
-- url     : https://prove2.me/theorems/fa4b9da8-d00b-43b3-8a77-0fd92690d547
-- title:
--   One Qubit Clifford
-- statement:
--   Definitions and structural lemmas for One Qubit Clifford, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitClifford.lean

import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC
namespace Distillation
namespace OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
inductive PauliAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr
instance : Fintype PauliAxis where
  elems := {PauliAxis.x, PauliAxis.y, PauliAxis.z}
  complete a := by cases a <;> simp
def permuteSigns (p : Equiv.Perm PauliAxis) : MulAut (PauliAxis → ℤˣ) where
  toFun s i := s (p.symm i)
  invFun s i := s (p i)
  left_inv s := by ext i; simp
  right_inv s := by ext i; simp
  map_mul' s t := by ext i; rfl
def signAction : Equiv.Perm PauliAxis →* MulAut (PauliAxis → ℤˣ) where
  toFun := permuteSigns
  map_one' := by ext s i; rfl
  map_mul' p q := by ext s i; rfl
abbrev SignedAxisPermutation :=
  SemidirectProduct (PauliAxis → ℤˣ) (Equiv.Perm PauliAxis) signAction
instance : Fintype SignedAxisPermutation :=
  Fintype.ofEquiv ((PauliAxis → ℤˣ) × Equiv.Perm PauliAxis)
    SemidirectProduct.equivProd.symm
def coordinateSign : (PauliAxis → ℤˣ) →* ℤˣ where
  toFun s := ∏ i, s i
  map_one' := by simp
  map_mul' s t := by simp only [Pi.mul_apply, Finset.prod_mul_distrib]
@[simp] theorem coordinateSign_signAction (p : Equiv.Perm PauliAxis)
    (s : PauliAxis → ℤˣ) : coordinateSign (signAction p s) = coordinateSign s :=
  p.symm.prod_comp s
def signedDeterminant : SignedAxisPermutation →* ℤˣ where
  toFun g := coordinateSign g.left * Equiv.Perm.sign g.right
  map_one' := by simp
  map_mul' a b := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    rw [coordinateSign_signAction]
    ac_rfl
abbrev ProjectiveClifford := signedDeterminant.ker
inductive SignedCoordinate where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr
instance : Fintype SignedCoordinate where
  elems := {SignedCoordinate.neg, SignedCoordinate.zero, SignedCoordinate.pos}
  complete a := by cases a <;> simp
def signCoordinate (s : ℤˣ) : SignedCoordinate → SignedCoordinate
  | .zero => .zero
  | .pos => if s = 1 then .pos else .neg
  | .neg => if s = 1 then .neg else .pos
instance : MulAction ℤˣ SignedCoordinate where
  smul := signCoordinate
  one_smul := by decide +kernel
  mul_smul := by decide +kernel
def signedAxisAction (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) : PauliAxis → SignedCoordinate :=
  fun i => g.left i • d (g.right.symm i)
instance : MulAction SignedAxisPermutation (PauliAxis → SignedCoordinate) where
  smul := signedAxisAction
  one_smul := by intro d; funext i; change (1 : ℤˣ) • d i = d i; exact one_smul _ _
  mul_smul := by intro g h d; funext i; change (g.left i * h.left (g.right.symm i)) • d (h.right.symm (g.right.symm i)) = g.left i • (h.left (g.right.symm i) • d (h.right.symm (g.right.symm i))); exact mul_smul _ _ _
def IsTDirection (d : PauliAxis → SignedCoordinate) : Prop :=
  ∀ i, d i ≠ .zero
def IsHDirection (d : PauliAxis → SignedCoordinate) : Prop :=
  (Finset.univ.filter fun i => d i = .zero).card = 1
instance (d : PauliAxis → SignedCoordinate) : Decidable (IsTDirection d) := by
  unfold IsTDirection
  infer_instance
instance (d : PauliAxis → SignedCoordinate) : Decidable (IsHDirection d) := by
  unfold IsHDirection
  infer_instance
abbrev TDirection := {d : PauliAxis → SignedCoordinate // IsTDirection d}
abbrev HDirection := {d : PauliAxis → SignedCoordinate // IsHDirection d}
theorem isTDirection_smul (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) :
    IsTDirection d → IsTDirection (g • d) := by
  revert g d
  decide +kernel
theorem isHDirection_smul (g : SignedAxisPermutation)
    (d : PauliAxis → SignedCoordinate) :
    IsHDirection d → IsHDirection (g • d) := by
  revert g d
  decide +kernel
instance : SMul SignedAxisPermutation TDirection where
  smul g d := ⟨g • d.1, isTDirection_smul g d.1 d.2⟩
instance : MulAction SignedAxisPermutation TDirection where
  one_smul d := by
    apply Subtype.ext
    change (1 : SignedAxisPermutation) • d.1 = d.1
    exact one_smul SignedAxisPermutation d.1
  mul_smul g h d := by
    apply Subtype.ext
    change (g * h) • d.1 = g • h • d.1
    exact mul_smul g h d.1
instance : SMul SignedAxisPermutation HDirection where
  smul g d := ⟨g • d.1, isHDirection_smul g d.1 d.2⟩
instance : MulAction SignedAxisPermutation HDirection where
  one_smul d := by
    apply Subtype.ext
    change (1 : SignedAxisPermutation) • d.1 = d.1
    exact one_smul SignedAxisPermutation d.1
  mul_smul g h d := by
    apply Subtype.ext
    change (g * h) • d.1 = g • h • d.1
    exact mul_smul g h d.1
def hadamardClifford : ProjectiveClifford :=
  ⟨⟨fun
      | .x => 1
      | .y => -1
      | .z => 1,
    Equiv.swap .x .z⟩,
    by decide +kernel⟩
def phaseClifford : ProjectiveClifford :=
  ⟨⟨fun
      | .x => -1
      | .y => 1
      | .z => 1,
    Equiv.swap .x .y⟩,
    by decide +kernel⟩
@[simp] theorem hadamardClifford_x (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .x = d .z := by
  change (1 : ℤˣ) • d .z = d .z
  simp
@[simp] theorem hadamardClifford_y (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .y = (-1 : ℤˣ) • d .y := by
  rfl
@[simp] theorem hadamardClifford_z (d : PauliAxis → SignedCoordinate) :
    (hadamardClifford.1 • d) .z = d .x := by
  change (1 : ℤˣ) • d .x = d .x
  simp
@[simp] theorem phaseClifford_x (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .x = (-1 : ℤˣ) • d .y := by
  rfl
@[simp] theorem phaseClifford_y (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .y = d .x := by
  change (1 : ℤˣ) • d .x = d .x
  simp
@[simp] theorem phaseClifford_z (d : PauliAxis → SignedCoordinate) :
    (phaseClifford.1 • d) .z = d .z := by
  change (1 : ℤˣ) • d .z = d .z
  simp
noncomputable section
def hadamardMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![(Real.sqrt 2 : Complex)⁻¹, (Real.sqrt 2 : Complex)⁻¹;
     (Real.sqrt 2 : Complex)⁻¹, -(Real.sqrt 2 : Complex)⁻¹]
def phaseMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, Complex.I]
def phaseInverseMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, -Complex.I]
def hadamardOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin hadamardMatrix
def phaseOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin phaseMatrix
def phaseInverseOperator : Operator QubitSpace :=
  Matrix.toEuclideanLin phaseInverseMatrix
theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.2 (by norm_num)
theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)
theorem sqrt_two_ne_zero_complex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_two_pos.ne'
theorem sqrt_two_mul_self_complex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self
theorem two_mul_inv_sqrt_two_sq :
    (2 : Complex) *
      ((Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) = 1 := by
  rw [← sqrt_two_mul_self_complex]
  field_simp [sqrt_two_ne_zero_complex]
@[simp] theorem hadamardOperator_apply_zero (psi : QubitSpace) :
    hadamardOperator psi 0 = (Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) := by
  simp [hadamardOperator, hadamardMatrix, Matrix.mulVec, dotProduct]
  ring
@[simp] theorem hadamardOperator_apply_one (psi : QubitSpace) :
    hadamardOperator psi 1 = (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1) := by
  simp [hadamardOperator, hadamardMatrix, Matrix.mulVec, dotProduct]
  ring
@[simp] theorem phaseOperator_apply_zero (psi : QubitSpace) :
    phaseOperator psi 0 = psi 0 := by
  simp [phaseOperator, phaseMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem phaseOperator_apply_one (psi : QubitSpace) :
    phaseOperator psi 1 = Complex.I * psi 1 := by
  simp [phaseOperator, phaseMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem phaseInverseOperator_apply_zero (psi : QubitSpace) :
    phaseInverseOperator psi 0 = psi 0 := by
  simp [phaseInverseOperator, phaseInverseMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem phaseInverseOperator_apply_one (psi : QubitSpace) :
    phaseInverseOperator psi 1 = -Complex.I * psi 1 := by
  simp [phaseInverseOperator, phaseInverseMatrix, Matrix.mulVec, dotProduct]
theorem hadamardOperator_square : hadamardOperator * hadamardOperator = 1 := by
  ext psi b
  fin_cases b
  · change hadamardOperator (hadamardOperator psi) 0 = psi 0
    rw [hadamardOperator_apply_zero, hadamardOperator_apply_zero,
      hadamardOperator_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) +
            (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1)) =
          (2 * ((Real.sqrt 2 : Complex)⁻¹ *
            (Real.sqrt 2 : Complex)⁻¹)) * psi 0 := by
            ring
      _ = psi 0 := by rw [two_mul_inv_sqrt_two_sq, one_mul]
  · change hadamardOperator (hadamardOperator psi) 1 = psi 1
    rw [hadamardOperator_apply_one, hadamardOperator_apply_zero,
      hadamardOperator_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) -
            (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1)) =
          (2 * ((Real.sqrt 2 : Complex)⁻¹ *
            (Real.sqrt 2 : Complex)⁻¹)) * psi 1 := by
            ring
      _ = psi 1 := by rw [two_mul_inv_sqrt_two_sq, one_mul]
theorem phaseOperator_phaseInverseOperator :
    phaseOperator * phaseInverseOperator = 1 := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, ← mul_assoc, Complex.I_mul_I]
theorem phaseInverseOperator_phaseOperator :
    phaseInverseOperator * phaseOperator = 1 := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, ← mul_assoc, Complex.I_mul_I]
def hadamardLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk hadamardOperator hadamardOperator
    (fun psi => by
      have h := LinearMap.congr_fun hadamardOperator_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun hadamardOperator_square psi
      simpa [Module.End.mul_apply] using h)
def phaseLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk phaseOperator phaseInverseOperator
    (fun psi => by
      have h := LinearMap.congr_fun phaseInverseOperator_phaseOperator psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun phaseOperator_phaseInverseOperator psi
      simpa [Module.End.mul_apply] using h)
@[simp] theorem hadamardLinearEquiv_apply (psi : QubitSpace) :
    hadamardLinearEquiv psi = hadamardOperator psi :=
  rfl
@[simp] theorem hadamardLinearEquiv_symm_apply (psi : QubitSpace) :
    hadamardLinearEquiv.symm psi = hadamardOperator psi :=
  rfl
@[simp] theorem phaseLinearEquiv_apply (psi : QubitSpace) :
    phaseLinearEquiv psi = phaseOperator psi :=
  rfl
@[simp] theorem phaseLinearEquiv_symm_apply (psi : QubitSpace) :
    phaseLinearEquiv.symm psi = phaseInverseOperator psi :=
  rfl
def hadamardTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := hadamardLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (hadamardOperator x) (hadamardOperator y) =
      inner Complex x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, hadamardOperator_apply_zero,
      hadamardOperator_apply_one, RCLike.inner_apply,
      map_add, map_sub, map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp [sqrt_two_ne_zero_complex]
    rw [pow_two, sqrt_two_mul_self_complex]
    ring
def phaseTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseLinearEquiv
  map_inner := by
    intro x y
    change inner Complex (phaseOperator x) (phaseOperator y) = inner Complex x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, phaseOperator_apply_zero,
      phaseOperator_apply_one, RCLike.inner_apply,
      map_mul, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
end
end OneQubitMagic
end Distillation
end QEC


