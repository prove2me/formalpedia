-- Prove2me | Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
-- name    : QEC_Coding_CodeReduction_DistanceBalancing_SubsystemDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:52:08.777674+00:00
-- url     : https://prove2.me/theorems/b56efcae-27b8-442c-930a-d4cee7314965
-- title:
--   Subsystem Dimension
-- statement:
--   Definitions and structural lemmas for Subsystem Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/SubsystemDimension.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Subsystem
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_productHomologyProjection_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancingSubsystem_sourceCohomologyProjection_surjective
import Theorems.Thm_QEC_Coding_DistanceBalancing_classicalKernelProjectionWord_mem_kernel
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_eq
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary1_apply_inl
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
variable (S : Matrix classicalBit classicalCheck (ZMod 2))
noncomputable abbrev ClassicalCokernelComplement :=
  LinearMap.ker
    (wordLinearMapTranspose (Matrix.toLin' S) :
      Word (ZMod 2) classicalBit →ₗ[ZMod 2]
        Word (ZMod 2) classicalCheck)
noncomputable def sourceCocycleSection :
    (sourceChainComplex (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      (sourceChainComplex (productData SD Y)).middleCocycleCode.carrier :=
  Classical.choose
    ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex
              (productData SD Y)).middleCoboundaryInCocycles)))
theorem sourceCocycleSection_spec
    (h : (sourceChainComplex (productData SD Y)).middleCohomology) :
    (sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
        (sourceCocycleSection SD Y h) = h := by
  have hRight := Classical.choose_spec
    ((sourceChainComplex (productData SD Y)).middleCoboundaryInCocycles.mkQ
      |>.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr
          (Submodule.mkQ_surjective
            (sourceChainComplex
              (productData SD Y)).middleCoboundaryInCocycles)))
  exact LinearMap.congr_fun hRight h
noncomputable def pureTensorCochain
    (h : (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalCokernelComplement S) :
    Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) :=
  Sum.elim
    (fun p => (sourceCocycleSection SD Y h).1 p.1 * w.1 p.2)
    (fun _ => 0)
theorem pureTensorCochain_mem_middleCocycleCode
    (h : (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalCokernelComplement S) :
    pureTensorCochain SD Y S h w ∈
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier := by
  rw [(DistanceBalancing.chainComplex
    (productData SD Y)).mem_middleCocycleCode_iff]
  ext p
  rcases p with ⟨x2, a⟩
  change wordLinearMapTranspose (DistanceBalancing.boundary2
    (productData SD Y)) (pureTensorCochain SD Y S h w) (x2, a) = 0
  rw [DistanceBalancing.transpose_boundary2_apply]
  have hCocycle := (sourceCocycleSection SD Y h).2
  have hZero := ((sourceChainComplex
    (productData SD Y)).mem_middleCocycleCode_iff _).mp hCocycle
  have hAt := congrFun hZero x2
  simp only [Pi.zero_apply] at hAt
  change wordLinearMapTranspose
    (Matrix.toLin' (productData SD Y).xBoundary2)
      (sourceCocycleSection SD Y h).1 x2 = 0 at hAt
  rw [wordLinearMapTranspose_toLin'_apply] at hAt
  have hAt' : (∑ x1 : xOne,
      (productData SD Y).xBoundary2 x1 x2 *
        (sourceCocycleSection SD Y h).1 x1) = 0 := by
    simpa [mul_comm] using hAt
  simp only [pureTensorCochain, xOneBitSlice, xTwoCheckSlice,
    Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
  calc
    (∑ x1 : xOne,
        (productData SD Y).xBoundary2 x1 x2 *
          ((sourceCocycleSection SD Y h).1 x1 * w.1 a)) =
        (∑ x1 : xOne,
          (productData SD Y).xBoundary2 x1 x2 *
            (sourceCocycleSection SD Y h).1 x1) * w.1 a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x1 _
      rw [mul_assoc]
    _ = 0 := by rw [hAt', zero_mul]
noncomputable def pureTensorCocycleBilinear :
    (sourceChainComplex (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      ClassicalCokernelComplement S →ₗ[ZMod 2]
        (DistanceBalancing.chainComplex
          (productData SD Y)).middleCocycleCode.carrier where
  toFun h :=
    { toFun := fun w =>
        ⟨pureTensorCochain SD Y S h w,
          pureTensorCochain_mem_middleCocycleCode SD Y S h w⟩
      map_add' := by
        intro w₁ w₂
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCochain] <;> ring
      map_smul' := by
        intro c w
        apply Subtype.ext
        ext q
        cases q <;> simp [pureTensorCochain] <;> ring }
  map_add' := by
    intro h₁ h₂
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCochain] <;> ring
  map_smul' := by
    intro c h
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    ext q
    cases q <;> simp [pureTensorCochain] <;> ring
noncomputable def tensorCocycleMap :
    (sourceChainComplex (productData SD Y)).middleCohomology ⊗[ZMod 2]
        ClassicalCokernelComplement S →ₗ[ZMod 2]
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier :=
  TensorProduct.lift (pureTensorCocycleBilinear SD Y S)
noncomputable def tensorCohomologyMap :
    (sourceChainComplex (productData SD Y)).middleCohomology ⊗[ZMod 2]
        ClassicalCokernelComplement S →ₗ[ZMod 2]
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCohomology :=
  (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ.comp
    (tensorCocycleMap SD Y S)
@[simp]
theorem tensorCohomologyMap_tmul
    (h : (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalCokernelComplement S) :
    tensorCohomologyMap SD Y S (h ⊗ₜ[ZMod 2] w) =
      (DistanceBalancing.chainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ
          ⟨pureTensorCochain SD Y S h w,
            pureTensorCochain_mem_middleCocycleCode SD Y S h w⟩ := by
  rfl
noncomputable def sourceZeroCochainContraction
    (u : Word (ZMod 2)
      (DistanceBalancing.C0Index xZero xOne classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit) : Word (ZMod 2) xZero :=
  fun x0 => ∑ a : classicalBit, c a * u (Sum.inl (x0, a))
theorem sourceCochainContraction_transpose_boundary1
    (u : Word (ZMod 2)
      (DistanceBalancing.C0Index xZero xOne classicalBit classicalCheck))
    (c : Word (ZMod 2) classicalBit)
    (hc : Matrix.toLin' (productData SD Y).classicalBoundary c = 0) :
    sourceCochainContraction
        (wordLinearMapTranspose
          (DistanceBalancing.boundary1 (productData SD Y)) u) c =
      wordLinearMapTranspose
        (sourceChainComplex (productData SD Y)).boundary1
          (sourceZeroCochainContraction u c) := by
  ext x1
  change sourceCochainContraction
      (wordLinearMapTranspose
        (DistanceBalancing.boundary1 (productData SD Y)) u) c x1 =
    wordLinearMapTranspose (Matrix.toLin'
      (productData SD Y).xBoundary1)
        (sourceZeroCochainContraction u c) x1
  rw [wordLinearMapTranspose_toLin'_apply]
  simp only [sourceCochainContraction, sourceZeroCochainContraction,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, xOneBitSlice]
  simp_rw [DistanceBalancing.transpose_boundary1_apply_inl]
  have hcAt : ∀ b : classicalCheck,
      (∑ a : classicalBit, Y (Pi.single a 1) b * c a) = 0 := by
    intro b
    have hc' : Y c = 0 := by
      simpa [productData, Matrix.toLin'_toMatrix'] using hc
    have hAt := congrFun hc' b
    simp only [Pi.zero_apply] at hAt
    calc
      (∑ a : classicalBit, Y (Pi.single a 1) b * c a) =
          Y (∑ a : classicalBit, c a • Pi.single a 1) b := by
        rw [map_sum]
        simp [mul_comm]
      _ = Y c b := by
        rw [show (∑ a : classicalBit, c a • Pi.single a 1) = c by
          calc
            (∑ a : classicalBit, c a • Pi.single a 1) =
                ∑ a : classicalBit, Pi.single a (c a) := by
              apply Finset.sum_congr rfl
              intro a _
              ext a'
              simp [Pi.single_apply, smul_eq_mul]
            _ = c := Finset.univ_sum_single c]
      _ = 0 := hAt
  calc
    (∑ a : classicalBit,
        c a *
          ((∑ x0 : xZero,
              (productData SD Y).xBoundary1 x0 x1 *
                u (Sum.inl (x0, a))) +
            ∑ b : classicalCheck,
              Y (Pi.single a 1) b *
                u (Sum.inr (x1, b)))) =
        (∑ x0 : xZero,
          (∑ a : classicalBit, c a * u (Sum.inl (x0, a))) *
            (productData SD Y).xBoundary1 x0 x1) +
          ∑ b : classicalCheck,
            (∑ a : classicalBit,
              Y (Pi.single a 1) b * c a) *
                u (Sum.inr (x1, b)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x0 _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      · simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = ∑ x0 : xZero,
        (∑ a : classicalBit, c a * u (Sum.inl (x0, a))) *
          (productData SD Y).xBoundary1 x0 x1 := by
      simp_rw [hcAt]
      simp
theorem projectedSourceCochain_mem_firstCoboundary_of_productCoboundary
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (x : Word (ZMod 2)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (DistanceBalancing.chainComplex
      (productData SD Y)).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) :
    projectedSourceCochain (productData SD Y) S x a ∈
      (sourceChainComplex
        (productData SD Y)).firstCoboundaryCheckCode.carrier := by
  rcases ((DistanceBalancing.chainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff x).mp hx with
    ⟨u, rfl⟩
  apply ((sourceChainComplex
    (productData SD Y)).mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨sourceZeroCochainContraction u
    (classicalKernelProjectionWord (productData SD Y) S a), ?_⟩
  rw [← sourceCochainContraction_transpose_boundary1 SD Y]
  · rfl
  · exact classicalKernelProjectionWord_mem_kernel
      (productData SD Y) S hS a
noncomputable def projectedSourceCochainLinear (a : classicalBit) :
    Word (ZMod 2)
        (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck) →ₗ[ZMod 2]
      Word (ZMod 2) xOne where
  toFun x := projectedSourceCochain (productData SD Y) S x a
  map_add' x y := by
    ext x1
    simp [projectedSourceCochain, sourceCochainContraction, xOneBitSlice,
      Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext x1
    simp [projectedSourceCochain, sourceCochainContraction, xOneBitSlice,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
noncomputable def projectedSourceCocycleMap
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (a : classicalBit) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      (sourceChainComplex
        (productData SD Y)).middleCocycleCode.carrier where
  toFun x := ⟨projectedSourceCochain (productData SD Y) S x.1 a,
    projectedSourceCochain_mem_middleCocycleCode
      (productData SD Y) S hS x.1 x.2 a⟩
  map_add' x y := by
    apply Subtype.ext
    exact (projectedSourceCochainLinear SD Y S a).map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (projectedSourceCochainLinear SD Y S a).map_smul c x.1
noncomputable def selectedCohomologySlice
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (a : classicalBit) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      LogicalX :=
  (sourceCohomologyProjection SD Y).comp
    ((sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ.comp
        (projectedSourceCocycleMap SD Y S hS a))
noncomputable def selectedCohomologyCycleSlices
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCocycleCode.carrier →ₗ[ZMod 2]
      classicalBit → LogicalX where
  toFun x := fun a => selectedCohomologySlice SD Y S hS a x
  map_add' x y := by
    funext a
    exact (selectedCohomologySlice SD Y S hS a).map_add x y
  map_smul' c x := by
    funext a
    exact (selectedCohomologySlice SD Y S hS a).map_smul c x
theorem middleCoboundaryInCocycles_le_ker_selectedCohomologyCycleSlices
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles ≤
      LinearMap.ker (selectedCohomologyCycleSlices SD Y S hS) := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  funext a
  change selectedCohomologySlice SD Y S hS a x = 0
  rw [selectedCohomologySlice, LinearMap.comp_apply, LinearMap.comp_apply]
  let p := projectedSourceCocycleMap SD Y S hS a x
  have hpBoundary : p ∈ (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles :=
    projectedSourceCochain_mem_firstCoboundary_of_productCoboundary
      SD Y S hS x.1 hx a
  have hClass : (sourceChainComplex
      (productData SD Y)).middleCoboundaryInCocycles.mkQ
        p = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles).mpr hpBoundary
  rw [hClass, map_zero]
noncomputable def selectedCohomologySliceMap
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      classicalBit → LogicalX :=
  (DistanceBalancing.chainComplex
      (productData SD Y)).middleCoboundaryInCocycles.liftQ
    (selectedCohomologyCycleSlices SD Y S hS)
    (middleCoboundaryInCocycles_le_ker_selectedCohomologyCycleSlices
      SD Y S hS)
@[simp]
theorem selectedCohomologySliceMap_mk
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (x : (DistanceBalancing.chainComplex
      (productData SD Y)).middleCocycleCode.carrier) :
    selectedCohomologySliceMap SD Y S hS
        ((DistanceBalancing.chainComplex
          (productData SD Y)).middleCoboundaryInCocycles.mkQ x) =
      selectedCohomologyCycleSlices SD Y S hS x := by
  rfl
theorem sourceCochainLift_pureTensorCochain_eq_zero
    (h : (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalCokernelComplement S)
    (b : classicalCheck) :
    sourceCochainLift S (pureTensorCochain SD Y S h w) b = 0 := by
  have hwZero := LinearMap.mem_ker.mp w.2
  have hwAt := congrFun hwZero b
  simp only [Pi.zero_apply] at hwAt
  rw [wordLinearMapTranspose_toLin'_apply] at hwAt
  ext x1
  simp only [sourceCochainLift, sourceCochainContraction,
    pureTensorCochain, xOneBitSlice, Sum.elim_inl,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  calc
    (∑ a : classicalBit,
        S a b * ((sourceCocycleSection SD Y h).1 x1 * w.1 a)) =
        (sourceCocycleSection SD Y h).1 x1 *
          (∑ a : classicalBit, w.1 a * S a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [hwAt, mul_zero]
theorem projectedSourceCochain_pureTensorCochain
    (h : (sourceChainComplex (productData SD Y)).middleCohomology)
    (w : ClassicalCokernelComplement S)
    (a : classicalBit) :
    projectedSourceCochain (productData SD Y) S
        (pureTensorCochain SD Y S h w) a =
      w.1 a • (sourceCocycleSection SD Y h).1 := by
  rw [projectedSourceCochain_eq]
  simp_rw [sourceCochainLift_pureTensorCochain_eq_zero SD Y S h w]
  ext x1
  simp [pureTensorCochain, xOneBitSlice, smul_eq_mul, mul_comm]
noncomputable def cokernelTensorToLogicalSlices :
    LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S →ₗ[ZMod 2]
      classicalBit → LogicalX :=
  (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalX classicalBit).toLinearMap.comp
    ((ClassicalCokernelComplement S).subtype.lTensor LogicalX)
@[simp]
theorem cokernelTensorToLogicalSlices_tmul
    (x : LogicalX) (w : ClassicalCokernelComplement S) :
    cokernelTensorToLogicalSlices S (x ⊗ₜ[ZMod 2] w) =
      fun a => w.1 a • x := by
  ext a
  simp [cokernelTensorToLogicalSlices,
    TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
theorem cokernelTensorToLogicalSlices_injective :
    Function.Injective (cokernelTensorToLogicalSlices
      (LogicalX := LogicalX) S) := by
  apply Function.Injective.comp
    (TensorProduct.piScalarRight (ZMod 2) (ZMod 2)
      LogicalX classicalBit).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (ClassicalCokernelComplement S).subtype
    (ClassicalCokernelComplement S).injective_subtype
noncomputable def cokernelTensorLogicalRetraction :
    (classicalBit → LogicalX) →ₗ[ZMod 2]
      LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S :=
  (cokernelTensorToLogicalSlices S).leftInverse
theorem cokernelTensorLogicalRetraction_apply
    (t : LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S) :
    cokernelTensorLogicalRetraction S
        (cokernelTensorToLogicalSlices S t) = t := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr
      (cokernelTensorToLogicalSlices_injective S)) t
noncomputable def sourceLogicalCohomTensorProjection :
    (sourceChainComplex (productData SD Y)).middleCohomology ⊗[ZMod 2]
        ClassicalCokernelComplement S →ₗ[ZMod 2]
      LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S :=
  TensorProduct.map (sourceCohomologyProjection SD Y) LinearMap.id
theorem selectedCohomologySliceMap_comp_tensorCohomologyMap
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (selectedCohomologySliceMap SD Y S hS).comp
        (tensorCohomologyMap SD Y S) =
      (cokernelTensorToLogicalSlices S).comp
        (sourceLogicalCohomTensorProjection SD Y S) := by
  apply TensorProduct.ext'
  intro h w
  ext a
  rw [LinearMap.comp_apply, tensorCohomologyMap_tmul,
    selectedCohomologySliceMap_mk]
  have hp : projectedSourceCochain (productData SD Y) S
      (pureTensorCochain SD Y S h w) a ∈
      (sourceChainComplex
        (productData SD Y)).middleCocycleCode.carrier :=
    projectedSourceCochain_mem_middleCocycleCode
      (productData SD Y) S hS
        (pureTensorCochain SD Y S h w)
        (pureTensorCochain_mem_middleCocycleCode SD Y S h w) a
  let p : (sourceChainComplex
      (productData SD Y)).middleCocycleCode.carrier :=
    ⟨projectedSourceCochain (productData SD Y) S
      (pureTensorCochain SD Y S h w) a, hp⟩
  change sourceCohomologyProjection SD Y
      ((sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ p) = _
  have hClass :
      (sourceChainComplex
        (productData SD Y)).middleCoboundaryInCocycles.mkQ
          p =
        w.1 a • h := by
    calc
      _ = (sourceChainComplex
          (productData SD Y)).middleCoboundaryInCocycles.mkQ
            (w.1 a • sourceCocycleSection SD Y h) := by
        congr 1
        apply Subtype.ext
        exact projectedSourceCochain_pureTensorCochain SD Y S h w a
      _ = w.1 a •
          (sourceChainComplex
            (productData SD Y)).middleCoboundaryInCocycles.mkQ
              (sourceCocycleSection SD Y h) :=
        (sourceChainComplex
          (productData SD Y)).middleCoboundaryInCocycles.mkQ.map_smul _ _
      _ = w.1 a • h := by rw [sourceCocycleSection_spec]
  rw [hClass, map_smul]
  simp [sourceLogicalCohomTensorProjection,
    cokernelTensorToLogicalSlices_tmul]
noncomputable def productCohomologyProjection
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    (DistanceBalancing.chainComplex
        (productData SD Y)).middleCohomology →ₗ[ZMod 2]
      LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S :=
  (cokernelTensorLogicalRetraction S).comp
    (selectedCohomologySliceMap SD Y S hS)
theorem productCohomologyProjection_tensorCohomologyMap
    (hS : IsClassicalRightInverse (productData SD Y) S)
    (t : (sourceChainComplex (productData SD Y)).middleCohomology ⊗[ZMod 2]
      ClassicalCokernelComplement S) :
    productCohomologyProjection SD Y S hS
        (tensorCohomologyMap SD Y S t) =
      sourceLogicalCohomTensorProjection SD Y S t := by
  rw [productCohomologyProjection, LinearMap.comp_apply]
  have hSlices := LinearMap.congr_fun
    (selectedCohomologySliceMap_comp_tensorCohomologyMap SD Y S hS) t
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hSlices
  rw [hSlices, cokernelTensorLogicalRetraction_apply]
theorem productCohomologyProjection_surjective
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    Function.Surjective (productCohomologyProjection SD Y S hS) := by
  intro x
  have hTensor : Function.Surjective
      (sourceLogicalCohomTensorProjection SD Y S) := by
    apply TensorProduct.map_surjective
    · exact sourceCohomologyProjection_surjective SD Y
    · intro w
      exact ⟨w, rfl⟩
  obtain ⟨t, rfl⟩ := hTensor x
  exact ⟨tensorCohomologyMap SD Y S t,
    productCohomologyProjection_tensorCohomologyMap SD Y S hS t⟩
theorem finrank_classicalCokernelComplement_eq_classicalKernel
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    Module.finrank (ZMod 2) (ClassicalCokernelComplement S) =
      Module.finrank (ZMod 2) (ClassicalKernel (productData SD Y)) := by
  let fY := Matrix.toLin' (productData SD Y).classicalBoundary
  let fS := Matrix.toLin' S
  have hComp : fY.comp fS = LinearMap.id := by
    have hS' : LinearMap.toMatrix' Y * S = 1 := by
      exact hS
    dsimp [fY, fS, productData]
    rw [← Matrix.toLin'_mul]
    rw [hS']
    simp
  have hLeft : Function.LeftInverse fY fS := by
    intro y
    exact LinearMap.congr_fun hComp y
  have hfYSurj : Function.Surjective fY := hLeft.surjective
  have hfSInj : Function.Injective fS := hLeft.injective
  have hYRange : Module.finrank (ZMod 2) (LinearMap.range fY) =
      Fintype.card classicalCheck := by
    rw [LinearMap.range_eq_top.mpr hfYSurj, finrank_top]
    simp
  have hSRange : Module.finrank (ZMod 2) (LinearMap.range fS) =
      Fintype.card classicalCheck := by
    have hNull := fS.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hfSInj, finrank_bot, add_zero] at hNull
    simpa using hNull
  have hTransposeRange : Module.finrank (ZMod 2)
      (LinearMap.range (wordLinearMapTranspose fS)) =
        Fintype.card classicalCheck := by
    calc
      _ = Module.finrank (ZMod 2) (LinearMap.range fS) := by
        exact HypergraphProduct.finrank_range_wordLinearMapTranspose_toLin'_eq S
      _ = Fintype.card classicalCheck := hSRange
  have hYNull := fY.finrank_range_add_finrank_ker
  have hTransposeNull :=
    (wordLinearMapTranspose fS).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2)
      (LinearMap.ker (wordLinearMapTranspose fS)) =
    Module.finrank (ZMod 2) (LinearMap.ker fY)
  have hYDomain : Module.finrank (ZMod 2)
      (Word (ZMod 2) classicalBit) = Fintype.card classicalBit := by simp
  rw [hYDomain, hYRange] at hYNull
  rw [hYDomain, hTransposeRange] at hTransposeNull
  omega
noncomputable def balancedSubsystemData
    (hS : IsClassicalRightInverse (productData SD Y) S) :
    SubsystemCSSData
      (DistanceBalancing.C0Index xZero xOne classicalBit classicalCheck)
      (DistanceBalancing.QubitIndex xOne xTwo classicalBit classicalCheck)
      (DistanceBalancing.C2Index xTwo classicalBit)
      (LogicalZ ⊗[ZMod 2] ClassicalKernel (productData SD Y))
      (LogicalX ⊗[ZMod 2] ClassicalCokernelComplement S) where
  complex := DistanceBalancing.chainComplex (productData SD Y)
  homologyProjection := productHomologyProjection SD Y
  cohomologyProjection := productCohomologyProjection SD Y S hS
  homologyProjection_surjective :=
    productHomologyProjection_surjective SD Y
  cohomologyProjection_surjective :=
    productCohomologyProjection_surjective SD Y S hS
  logical_finrank_eq := by
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct,
      SD.logical_finrank_eq,
      finrank_classicalCokernelComplement_eq_classicalKernel SD Y S hS]
end QEC.Coding.DistanceBalancingSubsystem


