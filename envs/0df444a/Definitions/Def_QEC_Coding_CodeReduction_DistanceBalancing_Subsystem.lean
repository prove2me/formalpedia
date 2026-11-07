-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:31:56.651193+00:00
-- url     : https://prove2.me/theorems/55803bb9-ffed-4010-8915-aa89c1e0f777
-- title:
--   Subsystem
-- statement:
--   Definitions and structural lemmas for Subsystem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Subsystem.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.DistanceBalancing.homologySliceMap_mk
attribute [local simp] QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.DistanceBalancingSubsystem
open QEC.Coding
open QEC.Coding.DistanceBalancing
open scoped TensorProduct
universe u v
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Nonempty classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable {LogicalZ LogicalX : Type v}
variable [AddCommGroup LogicalZ] [Module (ZMod 2) LogicalZ]
variable [AddCommGroup LogicalX] [Module (ZMod 2) LogicalX]
variable [Module.Finite (ZMod 2) LogicalZ]
variable [Module.Finite (ZMod 2) LogicalX]
variable (SD : SubsystemCSSData xZero xOne xTwo LogicalZ LogicalX)
variable (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
  Word (ZMod 2) classicalCheck)
noncomputable abbrev productData :=
  DistanceBalancing.Data.ofComplexes SD.complex Y
noncomputable def sourceToOriginal : ThreeTermChainMap
    (sourceChainComplex (productData SD Y)) SD.complex where
  map0 := LinearMap.id
  map1 := LinearMap.id
  map2 := LinearMap.id
  commutes_boundary1 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
  commutes_boundary2 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
noncomputable def originalToSource : ThreeTermChainMap SD.complex
    (sourceChainComplex (productData SD Y)) where
  map0 := LinearMap.id
  map1 := LinearMap.id
  map2 := LinearMap.id
  commutes_boundary1 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
  commutes_boundary2 := by
    ext w
    simpa [productData, sourceChainComplex,
      DistanceBalancing.Data.ofComplexes]
noncomputable def sourceHomologyProjection :
    (sourceChainComplex (productData SD Y)).middleHomology →ₗ[ZMod 2]
      LogicalZ :=
  SD.homologyProjection.comp (sourceToOriginal SD Y).inducedMiddleHomology
noncomputable def sourceCohomologyProjection :
    (sourceChainComplex (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      LogicalX :=
  SD.cohomologyProjection.comp
    (originalToSource SD Y).inducedMiddleCohomology
noncomputable def sourceLogicalTensorProjection :
    (sourceChainComplex (productData SD Y)).middleHomology ⊗[ZMod 2]
        ClassicalKernel (productData SD Y) →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  TensorProduct.map (sourceHomologyProjection SD Y) LinearMap.id
noncomputable def selectedHomologySliceMap :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleHomology →ₗ[ZMod 2]
      classicalBit → LogicalZ where
  toFun h := fun a => sourceHomologyProjection SD Y
    (homologySliceMap (productData SD Y) h a)
  map_add' h₁ h₂ := by
    funext a
    simp
  map_smul' c h := by
    funext a
    simp
noncomputable def kernelTensorToZLogicalSlices :
    LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) →ₗ[ZMod 2]
      classicalBit → LogicalZ :=
  (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalZ classicalBit).toLinearMap.comp
    ((ClassicalKernel (productData SD Y)).subtype.lTensor LogicalZ)
@[simp]
theorem kernelTensorToZLogicalSlices_tmul
    (z : LogicalZ) (w : ClassicalKernel (productData SD Y)) :
    kernelTensorToZLogicalSlices SD Y (z ⊗ₜ[ZMod 2] w) =
      fun a => w.1 a • z := by
  ext a
  simp [kernelTensorToZLogicalSlices,
    TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
noncomputable def kernelTensorZLogicalRetraction :
    (classicalBit → LogicalZ) →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  (kernelTensorToZLogicalSlices SD Y).leftInverse
noncomputable def productHomologyProjection :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleHomology →ₗ[ZMod 2]
      LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y) :=
  (kernelTensorZLogicalRetraction SD Y).comp
    (selectedHomologySliceMap SD Y)
noncomputable def selectedHomologySlices
    (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier) :
    classicalBit → LogicalZ :=
  fun a => sourceHomologyProjection SD Y
    (sourceHomologySlice (productData SD Y) z hz a)
def ProductDressedZDistanceAtLeast (d : Nat) : Prop :=
  ∀ (z : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCycleCode.carrier),
    selectedHomologySlices SD Y z hz ≠ 0 → d ≤ HammingWeight z
noncomputable def selectedCohomologySlices
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier) :
    classicalBit → LogicalX :=
  fun a => sourceCohomologyProjection SD Y
    ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
      ⟨projectedSourceCochain (productData SD Y) S x a, by
        simpa [productData] using
          projectedSourceCochain_mem_middleCocycleCode
            (productData SD Y) S hS x hx a⟩)
def ProductDressedXDistanceAtLeast
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (d : Nat) : Prop :=
  ∀ (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier),
    selectedCohomologySlices SD Y S hS x hx ≠ 0 →
      d ≤ HammingWeight x
end QEC.Coding.DistanceBalancingSubsystem


