-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:53:21.771304+00:00
-- url     : https://prove2.me/theorems/5cbc5afc-aa65-402a-a505-90ce1b40dade
-- title:
--   Subsystem Kernel
-- statement:
--   Definitions and structural lemmas for Subsystem Kernel, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemKernel.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productHomologyProjection_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_sourceCohomologyProjection_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_add
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary2_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_snd_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.DistanceBalancing.homologySliceMap_mk
attribute [local simp] QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_snd_apply
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


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
noncomputable abbrev ClassicalKernelDual :=
  Module.Dual (ZMod 2) (ClassicalKernel (productData SD Y))
noncomputable def kernelCochainContractionLinear
    (w : ClassicalKernel (productData SD Y)) :
    Word (ZMod 2)
        (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) →ₗ[ZMod 2]
      Word (ZMod 2) xOne where
  toFun x := sourceCochainContraction x w.1
  map_add' x y := by
    ext x1
    simp [sourceCochainContraction, xOneBitSlice, Finset.sum_add_distrib,
      mul_add]
  map_smul' c x := by
    ext x1
    simp [sourceCochainContraction, xOneBitSlice, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm]
theorem sourceCochainContraction_smul_kernel
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (c : ZMod 2) (w : Word (ZMod 2) classicalBit) :
    sourceCochainContraction x (c • w) =
      c • sourceCochainContraction x w := by
  ext x1
  simp only [sourceCochainContraction, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring
noncomputable def kernelCocycleContractionMap
    (w : ClassicalKernel (productData SD Y)) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      (sourceChainComplex
        (productData SD Y)).middleCocycleCode.carrier where
  toFun x := ⟨sourceCochainContraction x.1 w.1,
    sourceCochainContraction_mem_middleCocycleCode
      (productData SD Y) x.1 x.2 w.1 (LinearMap.mem_ker.mp w.2)⟩
  map_add' x y := by
    apply Subtype.ext
    exact (kernelCochainContractionLinear SD Y w).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (kernelCochainContractionLinear SD Y w).map_smul c x.1
noncomputable def selectedKernelCohomologyClass
    (w : ClassicalKernel (productData SD Y)) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2] LogicalX :=
  (sourceCohomologyProjection SD Y).comp
    ((sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ.comp
        (kernelCocycleContractionMap SD Y w))
noncomputable def selectedKernelCohomologyCycleMap :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX where
  toFun x :=
    { toFun := fun w => selectedKernelCohomologyClass SD Y w x
      map_add' := by
        intro w₁ w₂
        have hcontraction :
            kernelCocycleContractionMap SD Y (w₁ + w₂) x =
              kernelCocycleContractionMap SD Y w₁ x +
                kernelCocycleContractionMap SD Y w₂ x := by
          apply Subtype.ext
          exact sourceCochainContraction_add x.1 w₁.1 w₂.1
        simp only [selectedKernelCohomologyClass, LinearMap.comp_apply]
        rw [hcontraction, map_add, map_add]
      map_smul' := by
        intro c w
        have hcontraction :
            kernelCocycleContractionMap SD Y (c • w) x =
              c • kernelCocycleContractionMap SD Y w x := by
          apply Subtype.ext
          exact sourceCochainContraction_smul_kernel x.1 c w.1
        simp only [selectedKernelCohomologyClass, LinearMap.comp_apply]
        rw [hcontraction, map_smul, map_smul]
        rfl }
  map_add' x y := by
    apply LinearMap.ext
    intro w
    exact (selectedKernelCohomologyClass SD Y w).map_add x y
  map_smul' c x := by
    apply LinearMap.ext
    intro w
    exact (selectedKernelCohomologyClass SD Y w).map_smul c x
theorem kernelCochainContraction_mem_firstCoboundary_of_productCoboundary
    (w : ClassicalKernel (productData SD Y))
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).firstCoboundaryCheckCode.carrier) :
    sourceCochainContraction x w.1 ∈
      (sourceChainComplex
        (productData SD Y)).firstCoboundaryCheckCode.carrier := by
  rcases ((DistanceBalancing.chainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff x).mp hx with ⟨u, rfl⟩
  apply ((sourceChainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨sourceZeroCochainContraction u w.1, ?_⟩
  exact (sourceCochainContraction_transpose_boundary1 SD Y u w.1
    (LinearMap.mem_ker.mp w.2)).symm
theorem middleCoboundary_le_ker_selectedKernelCohomologyCycleMap :
    (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles ≤
      LinearMap.ker (selectedKernelCohomologyCycleMap SD Y) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro w
  change selectedKernelCohomologyClass SD Y w x = 0
  rw [selectedKernelCohomologyClass, LinearMap.comp_apply,
    LinearMap.comp_apply]
  let p := kernelCocycleContractionMap SD Y w x
  have hp : p ∈ (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles :=
    kernelCochainContraction_mem_firstCoboundary_of_productCoboundary
      SD Y w x.1 hx
  have hzero : (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ p = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles).mpr hp
  rw [hzero, map_zero]
noncomputable def kernelCohomologyProjection :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX :=
  (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles.liftQ
    (selectedKernelCohomologyCycleMap SD Y)
    (middleCoboundary_le_ker_selectedKernelCohomologyCycleMap SD Y)
@[simp]
theorem kernelCohomologyProjection_mk
    (x : (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier) :
    kernelCohomologyProjection SD Y
        ((DistanceBalancing.chainComplex
          (productData SD Y)).middleCoboundaryInCocycles.mkQ x) =
      selectedKernelCohomologyCycleMap SD Y x := rfl
noncomputable def classicalKernelRetraction :
    Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      ClassicalKernel (productData SD Y) :=
  (ClassicalKernel (productData SD Y)).subtype.leftInverse
@[simp]
theorem classicalKernelRetraction_apply
    (w : ClassicalKernel (productData SD Y)) :
    classicalKernelRetraction SD Y w.1 = w := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr
      (ClassicalKernel (productData SD Y)).injective_subtype) w
noncomputable def sourceLogicalCohomologySection :
    LogicalX →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology :=
  Classical.choose
    ((sourceCohomologyProjection SD Y).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sourceCohomologyProjection_surjective SD Y)))
@[simp]
theorem sourceLogicalCohomologySection_spec (x : LogicalX) :
    sourceCohomologyProjection SD Y
      (sourceLogicalCohomologySection SD Y x) = x := by
  have hRight := Classical.choose_spec
    ((sourceCohomologyProjection SD Y).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr
        (sourceCohomologyProjection_surjective SD Y)))
  exact LinearMap.congr_fun hRight x
noncomputable def cohomologyFamilyCochain
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology) :
    Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Sum.elim
    (fun p => (sourceCocycleSection SD Y (g (Pi.single p.2 1))).1 p.1)
    (fun _ => 0)
theorem xOneBitSlice_cohomologyFamilyCochain
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology)
    (a : classicalBit) :
    xOneBitSlice (cohomologyFamilyCochain SD Y g) a =
      (sourceCocycleSection SD Y (g (Pi.single a 1))).1 := by
  rfl
theorem cohomologyFamilyCochain_mem_middleCocycleCode
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology) :
    cohomologyFamilyCochain SD Y g ∈
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier := by
  rw [(DistanceBalancing.chainComplex
    (productData SD Y)).mem_middleCocycleCode_iff]
  ext p
  rcases p with ⟨x2, a⟩
  change wordLinearMapTranspose (DistanceBalancing.boundary2
    (productData SD Y)) (cohomologyFamilyCochain SD Y g) (x2, a) = 0
  rw [DistanceBalancing.transpose_boundary2_apply]
  have hCocycle := (sourceCocycleSection SD Y (g (Pi.single a 1))).2
  have hAt := congrFun
    (((sourceChainComplex
      (productData SD Y)).mem_middleCocycleCode_iff _).mp hCocycle) x2
  simp only [Pi.zero_apply] at hAt
  change wordLinearMapTranspose
    (Matrix.toLin' (productData SD Y).xBoundary2)
      (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x2 = 0 at hAt
  rw [wordLinearMapTranspose_toLin'_apply] at hAt
  simp only [xOneBitSlice_cohomologyFamilyCochain,
    cohomologyFamilyCochain, xTwoCheckSlice, Sum.elim_inr, mul_zero,
    Finset.sum_const_zero, add_zero]
  simp only [mul_comm] at hAt
  exact hAt
theorem cohomologyClass_sourceCochainContraction_family
    (g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalKernel (productData SD Y)) :
    (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ
        ⟨sourceCochainContraction (cohomologyFamilyCochain SD Y g) w.1,
          sourceCochainContraction_mem_middleCocycleCode
            (productData SD Y) (cohomologyFamilyCochain SD Y g)
            (cohomologyFamilyCochain_mem_middleCocycleCode SD Y g)
            w.1 (LinearMap.mem_ker.mp w.2)⟩ = g w.1 := by
  rw [← sourceCocycleSection_spec SD Y (g w.1)]
  congr 1
  apply Subtype.ext
  ext x1
  simp only [sourceCochainContraction, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, xOneBitSlice_cohomologyFamilyCochain]
  have hw : (∑ a : classicalBit, w.1 a • Pi.single a 1) = w.1 := by
    calc
      (∑ a : classicalBit, w.1 a • Pi.single a 1) =
          ∑ a : classicalBit, Pi.single a (w.1 a) := by
        apply Finset.sum_congr rfl
        intro a _
        ext a'
        simp [Pi.single_apply, smul_eq_mul]
      _ = w.1 := Finset.univ_sum_single w.1
  calc
    (∑ a : classicalBit,
        w.1 a * (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1) =
      (∑ a : classicalBit,
        w.1 a • sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1 := by
        change (∑ a : classicalBit,
          w.1 a * (sourceCocycleSection SD Y (g (Pi.single a 1))).1 x1) =
            (Submodule.subtype _
              (∑ a : classicalBit,
                w.1 a • sourceCocycleSection SD Y (g (Pi.single a 1)))) x1
        rw [map_sum]
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro a _
        rfl
    _ = (sourceCocycleSection SD Y
        (g (∑ a : classicalBit, w.1 a • Pi.single a 1))).1 x1 := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    _ = (sourceCocycleSection SD Y (g w.1)).1 x1 := by rw [hw]
theorem kernelCohomologyProjection_surjective :
    Function.Surjective (kernelCohomologyProjection SD Y) := by
  intro f
  let g : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCohomology :=
    (sourceLogicalCohomologySection SD Y).comp
      (f.comp (classicalKernelRetraction SD Y))
  let c : (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier :=
    ⟨cohomologyFamilyCochain SD Y g,
      cohomologyFamilyCochain_mem_middleCocycleCode SD Y g⟩
  refine ⟨(DistanceBalancing.chainComplex
    (productData SD Y)).middleCoboundaryInCocycles.mkQ c, ?_⟩
  rw [kernelCohomologyProjection_mk]
  apply LinearMap.ext
  intro w
  change sourceCohomologyProjection SD Y
      ((sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ
          (kernelCocycleContractionMap SD Y w c)) = f w
  rw [show (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ
        (kernelCocycleContractionMap SD Y w c) = g w.1 by
    exact cohomologyClass_sourceCochainContraction_family SD Y g w]
  change sourceCohomologyProjection SD Y
    (sourceLogicalCohomologySection SD Y
      (f (classicalKernelRetraction SD Y w.1))) = f w
  rw [sourceLogicalCohomologySection_spec, classicalKernelRetraction_apply]
noncomputable def balancedKernelSubsystemData :
    SubsystemCSSData
      (DistanceBalancing.C0Index xZero xOne classicalBit classicalCheck)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck)
      (DistanceBalancing.C2Index xTwo classicalBit)
      (LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y))
      (ClassicalKernel (productData SD Y) →ₗ[ZMod 2] LogicalX) where
  complex := DistanceBalancing.chainComplex (productData SD Y)
  homologyProjection := productHomologyProjection SD Y
  cohomologyProjection := kernelCohomologyProjection SD Y
  homologyProjection_surjective := productHomologyProjection_surjective SD Y
  cohomologyProjection_surjective := kernelCohomologyProjection_surjective SD Y
  logical_finrank_eq := by
    rw [Module.finrank_tensorProduct, Module.finrank_linearMap,
      SD.logical_finrank_eq, Nat.mul_comm]
end QEC.Coding.DistanceBalancingSubsystem


