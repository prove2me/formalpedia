-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
-- name    : QEC_Coding_FiberBundle_ExplicitFamily_CohomologyDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:24:10.869198+00:00
-- url     : https://prove2.me/theorems/c3addff7-fab7-41a2-8fcc-9cb2fad4070a
-- title:
--   Cohomology Dimension
-- statement:
--   Definitions and structural lemmas for Cohomology Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/CohomologyDimension.lean

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_mem_firstCoboundaryCheckCode
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCocoboundary_apply_eq_horizontal_add_vertical
import Theorems.Thm_QEC_Coding_FiberBundle_cycleFiberCoboundary_apply
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
namespace QEC.Coding.FiberBundle
universe u
theorem horizontalBaseLift_mem_middleCocycleCode
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x ∈
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier := by
  rw [mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero]
  funext bj
  rcases bj with ⟨b, j⟩
  rw [bundleCocoboundary_apply_eq_horizontal_add_vertical]
  simp only [horizontalBaseLift, zero_mul, Finset.sum_const_zero, add_zero,
    RandomTwist.fiberBundleData, multipleRotationCycleData, cycleData]
  rw [← Finset.mul_sum]
  have hEll : 2 ≤ ell := by
    have hPred : ell - 1 ≠ 0 := NeZero.ne (ell - 1)
    omega
  let f : Word (ZMod 2) (ZMod (ell * ell)) := fun _ => 1
  change x b * (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) = 0
  have hParity :
      (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) = 0 := by
    calc
      (∑ i : ZMod (ell * ell), cycleBoundary (ell * ell) i j) =
          cycleFiberCoboundary (ell * ell) f j := by
        simp [cycleFiberCoboundary, f]
      _ = 0 := by
        rw [cycleFiberCoboundary_apply (ell * ell) (by nlinarith)]
        change (1 + 1 : ZMod 2) = 0
        rw [one_add_one_eq_two]
        exact ZMod.natCast_self 2
  rw [hParity, mul_zero]
theorem wordLinearMapTranspose_randomBase_boundary
    {r : Nat} (baseSample : RandomBase.Sample r)
    (t : Word (ZMod 2) (Fin (3 * r))) :
    wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample)) t =
      baseCoboundary baseSample t := by
  classical
  funext b
  have htranspose {ι κ : Type} [Fintype ι] [Fintype κ]
      (A : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κ)
      (y : Word (ZMod 2) κ) (i : ι) :
      wordLinearMapTranspose A y i = ∑ k : κ, y k * A (Pi.single i 1) k := by
    rw [wordLinearMapTranspose]
    rfl
  rw [htranspose]
  unfold baseCoboundary
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single b]
  · simp
  · intro b' hne
    simp [hne]
noncomputable abbrev HHO20BaseCohomology
    {r : Nat} (baseSample : RandomBase.Sample r) :=
  Word (ZMod 2) (Fin (4 * r)) ⧸
    LinearMap.range
      (wordLinearMapTranspose
        (Matrix.toLin' (RandomBase.boundary baseSample)))
noncomputable def horizontalBaseLiftCocycleLinearMap
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Word (ZMod 2) (Fin (4 * r)) →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCocycleCode.carrier where
  toFun x := ⟨horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell)) x,
    horizontalBaseLift_mem_middleCocycleCode
      baseSample twistSample x⟩
  map_add' x y := by
    apply Subtype.ext
    exact horizontalBaseLift_add x y
  map_smul' coefficient x := by
    apply Subtype.ext
    funext q
    rcases q with bi | aj
    · rfl
    · rfl
noncomputable def baseCochainToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Word (ZMod 2) (Fin (4 * r)) →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCohomology :=
  let K := chainComplex
    (RandomTwist.fiberBundleData baseSample twistSample)
  K.middleCoboundaryInCocycles.mkQ.comp
    (horizontalBaseLiftCocycleLinearMap baseSample twistSample)
theorem baseCoboundaryRange_le_ker_baseCochainToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    LinearMap.range
        (wordLinearMapTranspose
          (Matrix.toLin' (RandomBase.boundary baseSample))) ≤
      LinearMap.ker
        (baseCochainToBundleCohomology baseSample twistSample) := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  rw [LinearMap.mem_ker]
  change
    (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).middleCoboundaryInCocycles.mkQ
      (horizontalBaseLiftCocycleLinearMap baseSample twistSample
        (wordLinearMapTranspose
          (Matrix.toLin' (RandomBase.boundary baseSample)) t)) = 0
  rw [wordLinearMapTranspose_randomBase_boundary]
  change
    (horizontalBaseLiftCocycleLinearMap baseSample twistSample
      (baseCoboundary baseSample t)) ∈
      LinearMap.ker
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleCoboundaryInCocycles.mkQ
  rw [Submodule.ker_mkQ]
  change horizontalBaseLift
      (baseZero := Fin (3 * r))
      (fiberZero := ZMod (ell * ell))
      (fiberOne := ZMod (ell * ell))
      (baseCoboundary baseSample t) ∈
    (chainComplex
      (RandomTwist.fiberBundleData baseSample twistSample)
      ).firstCoboundaryCheckCode.carrier
  rw [← bundleCoboundary_constantFiberWord_eq_horizontalBaseLift
    baseSample twistSample t]
  exact bundleCoboundary_mem_firstCoboundaryCheckCode
    (RandomTwist.fiberBundleData baseSample twistSample)
    (constantFiberWord (fiberZero := ZMod (ell * ell)) t)
noncomputable def baseCohomologyToBundleCohomology
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) :
    HHO20BaseCohomology baseSample →ₗ[ZMod 2]
      (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCohomology :=
  (LinearMap.range
    (wordLinearMapTranspose
      (Matrix.toLin' (RandomBase.boundary baseSample)))).liftQ
    (baseCochainToBundleCohomology baseSample twistSample)
    (baseCoboundaryRange_le_ker_baseCochainToBundleCohomology
      baseSample twistSample)
end QEC.Coding.FiberBundle


