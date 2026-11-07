-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:16:46.087819+00:00
-- url     : https://prove2.me/theorems/96df9c6a-bbd0-450a-b92f-d6100f1d9e33
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
structure Data
    (xZero xOne xTwo classicalBit classicalCheck : Type u)
    [Fintype xZero] [Fintype xOne] [Fintype xTwo]
    [Fintype classicalBit] [Fintype classicalCheck] where
  xBoundary1 : Matrix xZero xOne (ZMod 2)
  xBoundary2 : Matrix xOne xTwo (ZMod 2)
  classicalBoundary : Matrix classicalCheck classicalBit (ZMod 2)
  x_boundary_squared : xBoundary1 * xBoundary2 = 0
def ClassicalDistanceAtLeast
    {classicalBit classicalCheck : Type u}
    [Fintype classicalBit] [DecidableEq classicalBit]
    [Fintype classicalCheck]
    (H : Matrix classicalCheck classicalBit (ZMod 2))
    (d : Nat) : Prop :=
  ∀ w : Word (ZMod 2) classicalBit,
    Matrix.toLin' H w = 0 → w ≠ 0 → d ≤ HammingWeight w
noncomputable def Data.ofComplexes
    {xZero xOne xTwo classicalBit classicalCheck : Type u}
    [Fintype xZero] [DecidableEq xZero]
    [Fintype xOne] [DecidableEq xOne]
    [Fintype xTwo] [DecidableEq xTwo]
    [Fintype classicalBit] [DecidableEq classicalBit]
    [Fintype classicalCheck] [DecidableEq classicalCheck]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    Data xZero xOne xTwo classicalBit classicalCheck where
  xBoundary1 := LinearMap.toMatrix' X.boundary1
  xBoundary2 := LinearMap.toMatrix' X.boundary2
  classicalBoundary := LinearMap.toMatrix' Y
  x_boundary_squared := by
    rw [← LinearMap.toMatrix'_comp]
    rw [X.boundary_squared]
    simp
abbrev C0Index (xZero xOne classicalBit classicalCheck : Type u) :=
  Sum (xZero × classicalBit) (xOne × classicalCheck)
abbrev QubitIndex (xOne xTwo classicalBit classicalCheck : Type u) :=
  Sum (xOne × classicalBit) (xTwo × classicalCheck)
abbrev C2Index (xTwo classicalBit : Type u) := xTwo × classicalBit
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
def IsClassicalRightInverse
    (S : Matrix classicalBit classicalCheck (ZMod 2)) : Prop :=
  D.classicalBoundary * S = 1
noncomputable def sourceChainComplex :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo) where
  boundary1 := Matrix.toLin' D.xBoundary1
  boundary2 := Matrix.toLin' D.xBoundary2
  boundary_squared := by
    change (Matrix.toLin' D.xBoundary1).comp
      (Matrix.toLin' D.xBoundary2) = 0
    rw [← Matrix.toLin'_mul]
    rw [D.x_boundary_squared]
    simp
@[simp]
theorem sourceChainComplex_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    sourceChainComplex (Data.ofComplexes X Y) = X := by
  cases X
  simp [sourceChainComplex, Data.ofComplexes, Matrix.toLin'_toMatrix']
@[simp]
theorem classicalBoundary_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck) :
    (Data.ofComplexes X Y).classicalBoundary = LinearMap.toMatrix' Y := rfl
def boundary1Matrix :
    Matrix
      (C0Index xZero xOne classicalBit classicalCheck)
      (QubitIndex xOne xTwo classicalBit classicalCheck)
      (ZMod 2) :=
  fun r c =>
    match r, c with
    | Sum.inl (x0, a), Sum.inl (x1, a') =>
        if a = a' then D.xBoundary1 x0 x1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr (x1, b), Sum.inl (x1', a) =>
        if x1 = x1' then D.classicalBoundary b a else 0
    | Sum.inr (x1, b), Sum.inr (x2, b') =>
        if b = b' then D.xBoundary2 x1 x2 else 0
def boundary2Matrix :
    Matrix
      (QubitIndex xOne xTwo classicalBit classicalCheck)
      (C2Index xTwo classicalBit)
      (ZMod 2) :=
  fun r c =>
    match r, c with
    | Sum.inl (x1, a'), (x2, a) =>
        if a' = a then D.xBoundary2 x1 x2 else 0
    | Sum.inr (x2', b), (x2, a) =>
        if x2' = x2 then D.classicalBoundary b a else 0
@[simp]
theorem boundary1Matrix_inl_inl
    (x0 : xZero) (a a' : classicalBit) (x1 : xOne) :
    boundary1Matrix D (Sum.inl (x0, a)) (Sum.inl (x1, a')) =
      if a = a' then D.xBoundary1 x0 x1 else 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inl_inr
    (x0 : xZero) (a : classicalBit)
    (x2 : xTwo) (b : classicalCheck) :
    boundary1Matrix D (Sum.inl (x0, a)) (Sum.inr (x2, b)) = 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inr_inl
    (x1 x1' : xOne) (b : classicalCheck) (a : classicalBit) :
    boundary1Matrix D (Sum.inr (x1, b)) (Sum.inl (x1', a)) =
      if x1 = x1' then D.classicalBoundary b a else 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inr_inr
    (x1 : xOne) (b b' : classicalCheck) (x2 : xTwo) :
    boundary1Matrix D (Sum.inr (x1, b)) (Sum.inr (x2, b')) =
      if b = b' then D.xBoundary2 x1 x2 else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inl
    (x1 : xOne) (a' a : classicalBit) (x2 : xTwo) :
    boundary2Matrix D (Sum.inl (x1, a')) (x2, a) =
      if a' = a then D.xBoundary2 x1 x2 else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inr
    (x2' x2 : xTwo) (b : classicalCheck) (a : classicalBit) :
    boundary2Matrix D (Sum.inr (x2', b)) (x2, a) =
      if x2' = x2 then D.classicalBoundary b a else 0 := by
  rfl
theorem boundary1Matrix_mul_boundary2Matrix :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext r c
  rcases c with ⟨x2, a⟩
  cases r with
  | inl r =>
      rcases r with ⟨x0, a0⟩
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type, boundary1Matrix_inl_inl,
        boundary1Matrix_inl_inr, boundary2Matrix_inl,
        boundary2Matrix_inr, zero_mul, Finset.sum_const_zero, add_zero]
      by_cases haa : a0 = a
      · subst a0
        simp
        have hsquare := congrFun (congrFun D.x_boundary_squared x0) x2
        simpa [Matrix.mul_apply] using hsquare
      · simp [haa]
  | inr r =>
      rcases r with ⟨x1, b⟩
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type, boundary1Matrix_inr_inl,
        boundary1Matrix_inr_inr, boundary2Matrix_inl,
        boundary2Matrix_inr]
      simp
      rw [mul_comm (D.classicalBoundary b a)]
      exact ZModModule.add_self _
noncomputable def boundary1 :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) →ₗ[ZMod 2]
      Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck) :=
  Matrix.toLin' (boundary1Matrix D)
noncomputable def boundary2 :
    Word (ZMod 2) (C2Index xTwo classicalBit) →ₗ[ZMod 2]
      Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Matrix.toLin' (boundary2Matrix D)
theorem boundary_squared :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp
noncomputable def chainComplex :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck))
      (Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck))
      (Word (ZMod 2) (C2Index xTwo classicalBit)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D
def xOneBitSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) : Word (ZMod 2) xOne :=
  fun x1 => z (Sum.inl (x1, a))
def xTwoCheckSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (b : classicalCheck) : Word (ZMod 2) xTwo :=
  fun x2 => z (Sum.inr (x2, b))
def xTwoBitSlice
    (w : Word (ZMod 2) (C2Index xTwo classicalBit))
    (a : classicalBit) : Word (ZMod 2) xTwo :=
  fun x2 => w (x2, a)
noncomputable def sourceCochainContraction
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) : Word (ZMod 2) xOne :=
  ∑ a : classicalBit, c a • xOneBitSlice x a
theorem boundary1_apply_inl
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (x0 : xZero) (a : classicalBit) :
    boundary1 D z (Sum.inl (x0, a)) =
      ∑ x1 : xOne,
        D.xBoundary1 x0 x1 * xOneBitSlice z a x1 := by
  rw [boundary1, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  simp [Fintype.sum_prod_type, xOneBitSlice]
noncomputable def classicalKernelProjectionWord
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (a : classicalBit) : Word (ZMod 2) classicalBit :=
  Pi.single a 1 + Matrix.toLin' S
    (Matrix.toLin' D.classicalBoundary (Pi.single a 1))
noncomputable def sourceCochainLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (b : classicalCheck) : Word (ZMod 2) xOne :=
  sourceCochainContraction x (fun a => S a b)
noncomputable def projectedSourceCochain
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) : Word (ZMod 2) xOne :=
  sourceCochainContraction x (classicalKernelProjectionWord D S a)
noncomputable def projectedSourceCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) : Word (ZMod 2) xZero :=
  Classical.choose
    (((sourceChainComplex D).mem_firstCoboundaryCheckCode_iff
      (projectedSourceCochain D S x a)).1 (hFill a))
noncomputable def productCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    Word (ZMod 2) (C0Index xZero xOne classicalBit classicalCheck) :=
  Sum.elim
    (fun p => projectedSourceCochainFilling D S x hFill p.2 p.1)
    (fun p => sourceCochainLift S x p.2 p.1)
theorem xOneBitSlice_mem_middleCycleCode
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    xOneBitSlice z a ∈ (sourceChainComplex D).middleCycleCode.carrier := by
  rw [(sourceChainComplex D).mem_middleCycleCode_iff]
  have hzZero := ((chainComplex D).mem_middleCycleCode_iff z).1 hz
  change boundary1 D z = 0 at hzZero
  ext x0
  have hAt := congrFun hzZero (Sum.inl (x0, a))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inl] at hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, xOneBitSlice] using hAt
noncomputable def sourceCycleSlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    (sourceChainComplex D).middleCycleCode.carrier :=
  ⟨xOneBitSlice z a, xOneBitSlice_mem_middleCycleCode D z hz a⟩
noncomputable def sourceHomologySlice
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) : (sourceChainComplex D).middleHomology :=
  (sourceChainComplex D).middleBoundaryInCycles.mkQ
    (sourceCycleSlice D z hz a)
noncomputable def classicalWordOfHomologyFunctional
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    Word (ZMod 2) classicalBit :=
  fun a => φ (sourceHomologySlice D z hz a)
noncomputable def xTwoBitFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (a : classicalBit) : Word (ZMod 2) xTwo :=
  Classical.choose
    (((sourceChainComplex D).mem_middleBoundaryCode_iff
      (xOneBitSlice z a)).1 (hFill a))
noncomputable def productSliceFilling
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (C2Index xTwo classicalBit) :=
  fun p => xTwoBitFilling D z hFill p.2 p.1
noncomputable def sliceRemainder
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (QubitIndex xOne xTwo classicalBit classicalCheck) :=
  z + boundary2 D (productSliceFilling D z hFill)
noncomputable def residualLift
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    Word (ZMod 2) (C2Index xTwo classicalBit) :=
  fun p =>
    ∑ b : classicalCheck,
      S p.2 b * sliceRemainder D z hFill (Sum.inr (p.1, b))
end QEC.Coding.DistanceBalancing


