-- Prove2me | Definitions.Def_GroundTheory_Brauer_Splitting
-- name    : GroundTheory_Brauer_Splitting
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:22:23.562809+00:00
-- url     : https://prove2.me/theorems/8d1aad68-e488-4bca-a23e-f5041f98f8f8
-- title:
--   Splitting
-- statement:
--   Definitions and structural lemmas for Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_degree_baseChangeCSA
import Theorems.Thm_GroundTheory_Brauer_degree_matrixCSA
import Theorems.Thm_GroundTheory_Brauer_degree_tensorCSA
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
import Theorems.Thm_GroundTheory_Brauer_tensorCentralizerAlgEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.BrauerGroup.baseChange_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.degree_baseChangeCSA
attribute [local simp] GroundTheory.Brauer.degree_matrixCSA
attribute [local simp] GroundTheory.Brauer.degree_tensorCSA
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier
attribute [local simp] GroundTheory.Brauer.tensorCentralizerAlgEquiv_tmul


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct Module
universe u v w
section SubalgebraOfDivisionRing
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
theorem inv_mem_of_finiteDimensional (S : Subalgebra K D) [FiniteDimensional K S] {x : D}
    (hx : x ∈ S) : x⁻¹ ∈ S := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero]; exact S.zero_mem
  let f : S →ₗ[K] S := LinearMap.mulLeft K (⟨x, hx⟩ : S)
  have hf : Function.Injective f := by
    intro a b hab
    have h : x * (a : D) = x * b := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel₀ h0 h)
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hf) 1
  have h1 : x * (b : D) = 1 := congrArg Subtype.val hb
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact b.2
noncomputable abbrev divisionRingOfFiniteDimensional (S : Subalgebra K D)
    [FiniteDimensional K S] : DivisionRing S :=
  DivisionRing.ofIsUnitOrEqZero fun a ↦ by
    by_cases h : a = 0
    · exact Or.inr h
    · refine Or.inl ⟨⟨a, ⟨(a : D)⁻¹, inv_mem_of_finiteDimensional S a.2⟩, ?_, ?_⟩, rfl⟩
      · exact Subtype.ext (mul_inv_cancel₀ fun h' ↦ h (Subtype.ext h'))
      · exact Subtype.ext (inv_mul_cancel₀ fun h' ↦ h (Subtype.ext h'))
noncomputable abbrev fieldOfIsMulCommutative (S : Subalgebra K D) [FiniteDimensional K S]
    [IsMulCommutative S] : Field S :=
  { divisionRingOfFiniteDimensional S with
    mul_comm := fun a b ↦ (isMulCommutative_iff.mp inferInstance) a b }
end SubalgebraOfDivisionRing
section SplitByEmbedding
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]
def RightMul (_ι : L →ₐ[K] A) : Type _ := A
namespace RightMul
variable (ι : L →ₐ[K] A)
instance : AddCommGroup (RightMul ι) := inferInstanceAs (AddCommGroup A)
instance : Module K (RightMul ι) := inferInstanceAs (Module K A)
instance : Module Aᵐᵒᵖ (RightMul ι) := inferInstanceAs (Module Aᵐᵒᵖ A)
def toOp : L →+* Aᵐᵒᵖ :=
  (ι.toOpposite fun x y ↦ (Commute.all x y).map ι).toRingHom
instance : Module L (RightMul ι) := Module.compHom (RightMul ι) (toOp ι)
def of (x : A) : RightMul ι := x
def val {ι : L →ₐ[K] A} (x : RightMul ι) : A := x
@[simp] theorem val_of (x : A) : (of ι x).val = x := rfl
@[simp] theorem of_val (x : RightMul ι) : of ι x.val = x := rfl
theorem val_smul_K (k : K) (x : RightMul ι) : (k • x).val = k • x.val := rfl
instance : IsScalarTower K L (RightMul ι) where
  smul_assoc k l x := by
    change x.val * ι (k • l) = k • (x.val * ι l)
    rw [map_smul, mul_smul_comm]
instance : SMulCommClass L K (RightMul ι) where
  smul_comm l k x := by
    change (k • x.val) * ι l = k • (x.val * ι l)
    rw [smul_mul_assoc]
instance [FiniteDimensional K A] : FiniteDimensional K (RightMul ι) :=
  inferInstanceAs (FiniteDimensional K A)
instance [Nontrivial A] : Nontrivial (RightMul ι) := inferInstanceAs (Nontrivial A)
def leftMul (a : A) : Module.End L (RightMul ι) where
  toFun x := of ι (a * x.val)
  map_add' x y := mul_add a x.val y.val
  map_smul' l x := (mul_assoc a x.val (ι l)).symm
def leftMulAlgHom : A →ₐ[K] Module.End L (RightMul ι) where
  toFun := leftMul ι
  map_one' := LinearMap.ext fun x ↦ one_mul x.val
  map_mul' a b := LinearMap.ext fun x ↦ mul_assoc a b x.val
  map_zero' := LinearMap.ext fun x ↦ zero_mul x.val
  map_add' a b := LinearMap.ext fun x ↦ add_mul a b x.val
  commutes' k := LinearMap.ext fun x ↦ by
    change algebraMap K A k * x.val = (k • x).val
    rw [val_smul_K, Algebra.smul_def]
noncomputable def actionHom : L ⊗[K] A →ₐ[L] Module.End L (RightMul ι) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (leftMulAlgHom ι)
    fun l a ↦ Algebra.commutes l (leftMulAlgHom ι a)
end RightMul
end SplitByEmbedding
section MaximalSubfield
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
variable [Algebra.IsCentral K D] [FiniteDimensional K D]
end MaximalSubfield
section Splitting
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
end Splitting
section SeparableSplitting
variable {K : Type u} [Field K]
end SeparableSplitting
end GroundTheory.Brauer


