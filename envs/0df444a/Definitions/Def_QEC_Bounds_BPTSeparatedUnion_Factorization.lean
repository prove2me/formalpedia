-- Prove2me | Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Factorization
-- name    : QEC_Bounds_BPTSeparatedUnion_Factorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:16:31.911205+00:00
-- url     : https://prove2.me/theorems/885b5e23-c9aa-4711-b709-01d935a74f57
-- title:
--   Factorization
-- statement:
--   Definitions and structural lemmas for Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Factorization.lean

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
def splitUnionSelectedLabel
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (labels : Semantics.Qudit.Label
      (M.regionSubsystem (left ∪ right)).selectedDimensions) :
    Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
      Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions :=
  (fun site => labels ⟨site, Finset.mem_union_left right site.property⟩,
    fun site => labels ⟨site, Finset.mem_union_right left site.property⟩)
def recombineUnionSelectedLabel
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (labels : Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
      Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) :
    Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions :=
  fun site => if hleft : (site : L.Site) ∈ left then
    labels.1 ⟨site, hleft⟩
  else
    labels.2 ⟨site, (Finset.mem_union.mp site.property).resolve_left hleft⟩
def unionSelectedLabelFactorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions ≃
      Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions ×
        Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions where
  toFun := M.splitUnionSelectedLabel left right
  invFun := M.recombineUnionSelectedLabel left right
  left_inv := by
    intro labels
    funext site
    by_cases hleft : (site : L.Site) ∈ left
    · simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
    · simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
  right_inv := by
    rintro ⟨leftLabels, rightLabels⟩
    apply Prod.ext
    · funext site
      have hleft : (site : L.Site) ∈ left := site.property
      simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hleft]
    · funext site
      have hnotleft : (site : L.Site) ∉ left := by
        intro hleft
        exact (Finset.disjoint_left.mp hdisjoint) hleft site.property
      simp [splitUnionSelectedLabel, recombineUnionSelectedLabel, hnotleft]
noncomputable def unionSelectedFactorization
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hdisjoint : Disjoint left right) :
    Semantics.UnitaryTransport (M.regionSubsystem (left ∪ right)).selectedSystem
      (Semantics.CompositeSystem (M.regionSubsystem left).selectedSystem
        (M.regionSubsystem right).selectedSystem) := by
  let sourceBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem (left ∪ right)).selectedDimensions) Complex
  let leftBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem left).selectedDimensions) Complex
  let rightBasis := EuclideanSpace.basisFun
    (Semantics.Qudit.Label (M.regionSubsystem right).selectedDimensions) Complex
  let targetBasis := leftBasis.tensorProduct rightBasis
  let U := sourceBasis.equiv targetBasis (M.unionSelectedLabelFactorization left right hdisjoint)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
end BPTCommutingProjectorModel
end Bounds
end QEC


