-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
-- name    : QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:12:55.728292+00:00
-- url     : https://prove2.me/theorems/da8d4894-a787-4611-8523-e778862ec4df
-- title:
--   Strip Logical Path
-- statement:
--   Definitions and structural lemmas for Strip Logical Path, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/StripLogicalPath.lean

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_append
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_nil
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_append_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_empty
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_reverse
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_take
import Theorems.Thm_QEC_Coding_PauliErrorPath_foldl_binaryMul_eq_binaryMul_accumulate
import Theorems.Thm_QEC_Coding_PauliErrorPath_reverse_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_zero
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_getLast_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_head_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_take_increments
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_btExcessEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_length_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_regionUnion_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_syndromeSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pathHeight_empty
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_alternatingWidths
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeSupport_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeWeight_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_unitDefectEnergy_binaryOne
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryDagger
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryOne
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
import Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliErrorPath.accumulate_nil
attribute [local simp] QEC.Coding.PauliErrorPath.accumulate_singleton
attribute [local simp] QEC.Coding.PauliErrorPath.append_increments
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_empty
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_reverse
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_singleton
attribute [local simp] QEC.Coding.PauliErrorPath.endpoint_take
attribute [local simp] QEC.Coding.PauliErrorPath.reverse_increments
attribute [local simp] QEC.Coding.PauliErrorPath.stateAt_length
attribute [local simp] QEC.Coding.PauliErrorPath.stateAt_zero
attribute [local simp] QEC.Coding.PauliErrorPath.states_getLast_eq_some
attribute [local simp] QEC.Coding.PauliErrorPath.states_head_eq_some
attribute [local simp] QEC.Coding.PauliErrorPath.states_length
attribute [local simp] QEC.Coding.PauliErrorPath.take_increments
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryDagger
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.btExcessEnergy_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.length_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_regionUnion_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_syndromeSupport
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pathHeight_empty
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_alternatingWidths
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeSupport_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeWeight_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.unitDefectEnergy_binaryOne
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryDagger
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryOne
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace PauliErrorPath
theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide
def siteFactor (Q : Binary ι) (i : ι) : Binary ι :=
  Locality.restrictBinaryTo {i} Q
theorem support_siteFactor_subset (Q : Binary ι) (i : ι) :
    support (siteFactor Q i) ⊆ {i} :=
  Locality.support_restrictBinaryTo_subset {i} Q
theorem weight_siteFactor_le_one (Q : Binary ι) (i : ι) :
    weight (siteFactor Q i) ≤ 1 := by
  exact (Finset.card_le_card (support_siteFactor_subset Q i)).trans (by simp)
omit [DecidableEq ι] in
theorem accumulate_cons (step : Binary ι) (steps : List (Binary ι)) :
    accumulate (step :: steps) = binaryMul step (accumulate steps) := by
  simp only [accumulate, List.foldl_cons, binaryMul_binaryOne_left]
  exact foldl_binaryMul_eq_binaryMul_accumulate steps step
theorem accumulate_map_siteFactor_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (accumulate (sites.map (siteFactor Q))).vector =
      (Locality.restrictBinaryTo sites.toFinset Q).vector := by
  induction sites with
  | nil =>
      change
        ({ xPart := 0, zPart := 0 } : SymplecticVector (ZMod 2) ι) =
          { xPart := fun _ => 0, zPart := fun _ => 0 }
      rfl
  | cons i sites ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, accumulate_cons]
      have ihVector := ih hnodup.2
      change
        (siteFactor Q i).vector +
            (accumulate (sites.map (siteFactor Q))).vector =
          (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector
      rw [ihVector]
      apply
        (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
      apply Prod.ext
      · funext q
        change
          ((siteFactor Q i).vector +
              (Locality.restrictBinaryTo sites.toFinset Q).vector).xPart q =
            (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector.xPart q
        by_cases hqi : q = i
        · subst q
          simp [siteFactor, Locality.restrictBinaryTo, hnodup.1]
        · simp [siteFactor, Locality.restrictBinaryTo, hqi]
      · funext q
        change
          ((siteFactor Q i).vector +
              (Locality.restrictBinaryTo sites.toFinset Q).vector).zPart q =
            (Locality.restrictBinaryTo (i :: sites).toFinset Q).vector.zPart q
        by_cases hqi : q = i
        · subst q
          simp [siteFactor, Locality.restrictBinaryTo, hnodup.1]
        · simp [siteFactor, Locality.restrictBinaryTo, hqi]
def orderedCore (Q : Binary ι) (sites : List ι) (_hnodup : sites.Nodup) :
    PauliErrorPath (ι := ι) where
  increments := sites.map (siteFactor Q)
  step_weight_le_one := by
    intro step hstep
    rw [List.mem_map] at hstep
    obtain ⟨i, _hi, rfl⟩ := hstep
    exact weight_siteFactor_le_one Q i
@[simp]
theorem orderedCore_increments
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (orderedCore Q sites hnodup).increments = sites.map (siteFactor Q) :=
  rfl
theorem orderedCore_endpoint_vector
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup) :
    (orderedCore Q sites hnodup).endpoint.vector =
      (Locality.restrictBinaryTo sites.toFinset Q).vector :=
  accumulate_map_siteFactor_vector Q sites hnodup
def orderedExact
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    PauliErrorPath (ι := ι) :=
  let core := orderedCore Q sites hnodup
  let correction := binaryMul (binaryDagger core.endpoint) Q
  {
    increments := core.increments ++ [correction]
    step_weight_le_one := by
      intro step hstep
      rcases List.mem_append.mp hstep with hcore | hcorrection
      · exact core.step_weight_le_one step hcore
      · have hstepEq : step = correction := by
          simpa using hcorrection
        subst step
        have hvector : correction.vector = 0 := by
          change core.endpoint.vector + Q.vector = 0
          rw [orderedCore_endpoint_vector Q sites hnodup, hcover]
          apply
            (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
          apply Prod.ext
          · funext i
            change
              ((Locality.restrictBinaryTo Finset.univ Q).vector +
                  Q.vector).xPart i = (0 : SymplecticVector (ZMod 2) ι).xPart i
            simp [Locality.restrictBinaryTo, zmod_two_add_self]
          · funext i
            change
              ((Locality.restrictBinaryTo Finset.univ Q).vector +
                  Q.vector).zPart i = (0 : SymplecticVector (ZMod 2) ι).zPart i
            simp [Locality.restrictBinaryTo, zmod_two_add_self]
        have hsupp : support correction = ∅ := by
          ext i
          simp [support, xSupport, zSupport, binarySupport, hvector]
        rw [weight, hsupp]
        simp
  }
@[simp]
theorem orderedExact_increments
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    (orderedExact Q sites hnodup hcover).increments =
      (orderedCore Q sites hnodup).increments ++
        [binaryMul (binaryDagger (orderedCore Q sites hnodup).endpoint) Q] :=
  rfl
@[simp]
theorem orderedExact_endpoint
    (Q : Binary ι) (sites : List ι) (hnodup : sites.Nodup)
    (hcover : sites.toFinset = Finset.univ) :
    (orderedExact Q sites hnodup hcover).endpoint = Q := by
  rw [endpoint, orderedExact_increments, accumulate_append]
  rw [accumulate_singleton, ← binaryMul_assoc]
  have hright :
      binaryMul (orderedCore Q sites hnodup).endpoint
          (binaryDagger (orderedCore Q sites hnodup).endpoint) =
        binaryOne := by
    rcases (orderedCore Q sites hnodup).endpoint with ⟨phase, ⟨x, z⟩⟩
    simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase,
      binaryOne]
    have htwo (a : ZMod 2) : a + a = 0 := by
      fin_cases a <;> decide
    constructor
    · have htwo (a : ZMod 2) : a + a = 0 := by
        fin_cases a <;> decide
      let s : ZMod 2 := ∑ i, x i * z i
      change phase + (phase + s) + s = 0
      calc
        phase + (phase + s) + s = (phase + phase) + (s + s) := by abel
        _ = 0 := by simp [htwo]
    · constructor <;> funext i
      · change x i + x i = 0
        exact htwo (x i)
      · change z i + z i = 0
        exact htwo (z i)
  change
    binaryMul
        (binaryMul (orderedCore Q sites hnodup).endpoint
          (binaryDagger (orderedCore Q sites hnodup).endpoint)) Q =
      Q
  rw [hright]
  simp
end PauliErrorPath
namespace StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
def rowMajorIndex {L : Nat} (p : Site L) : Nat :=
  p.2.val * L + p.1.val
theorem rowMajorIndex_eq_finProdFinEquiv_val
    {L : Nat} (p : Site L) :
    rowMajorIndex p = (finProdFinEquiv (p.2, p.1)).val := by
  simp [rowMajorIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
def rowMajorSites (L : Nat) : List (Site L) :=
  List.ofFn fun n : Fin (L * L) =>
    let yx : Fin L × Fin L := finProdFinEquiv.symm n
    (yx.2, yx.1)
@[simp]
theorem length_rowMajorSites (L : Nat) :
    (rowMajorSites L).length = L * L := by
  simp [rowMajorSites]
theorem rowMajorSites_nodup (L : Nat) :
    (rowMajorSites L).Nodup := by
  rw [rowMajorSites, List.nodup_ofFn]
  intro a b hab
  have hyx :
      finProdFinEquiv.symm a = finProdFinEquiv.symm b := by
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  exact finProdFinEquiv.symm.injective hyx
@[simp]
theorem rowMajorIndex_rowMajorSites_getElem
    {L n : Nat} (hn : n < (rowMajorSites L).length) :
    rowMajorIndex (rowMajorSites L)[n] = n := by
  simp only [rowMajorSites, List.getElem_ofFn]
  rw [rowMajorIndex_eq_finProdFinEquiv_val]
  exact
    congrArg Fin.val
      (finProdFinEquiv.apply_symm_apply ⟨n, by simpa using hn⟩)
theorem rowMajorSites_getElem_rowMajorIndex
    {L : Nat} (p : Site L)
    (hindex : rowMajorIndex p < (rowMajorSites L).length) :
    (rowMajorSites L)[rowMajorIndex p]'hindex = p := by
  have hindex' : rowMajorIndex p < L * L := by
    simpa [length_rowMajorSites] using hindex
  have hfin :
      (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L)) =
        finProdFinEquiv (p.2, p.1) := by
    apply Fin.ext
    exact rowMajorIndex_eq_finProdFinEquiv_val p
  simp only [rowMajorSites, List.getElem_ofFn]
  change
    ((finProdFinEquiv.symm
        (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L))).2,
      (finProdFinEquiv.symm
        (⟨rowMajorIndex p, hindex'⟩ : Fin (L * L))).1) = p
  rw [hfin, finProdFinEquiv.symm_apply_apply]
@[simp]
theorem rowMajorSites_toFinset (L : Nat) :
    (rowMajorSites L).toFinset =
      (Finset.univ : Finset (Site L)) := by
  ext p
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  have hindex : rowMajorIndex p < (rowMajorSites L).length := by
    rw [length_rowMajorSites, rowMajorIndex_eq_finProdFinEquiv_val]
    exact (finProdFinEquiv (p.2, p.1)).isLt
  exact
    List.mem_iff_getElem.mpr
      ⟨rowMajorIndex p, hindex,
        rowMajorSites_getElem_rowMajorIndex p hindex⟩
def rowMajorPrefix (L n : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p => rowMajorIndex p < n
def rowMajorExactPath {L : Nat} (Q : Binary (Site L)) :
    PauliErrorPath (ι := Site L) :=
  PauliErrorPath.orderedExact Q (rowMajorSites L)
    (rowMajorSites_nodup L) (rowMajorSites_toFinset L)
def openHorizontalInterval (L start width : Nat) : Finset (Site L) :=
  Finset.univ.filter fun p =>
    start ≤ p.2.val ∧ p.2.val < start + width
def periodicHorizontalInterval (L start width : Nat) : Finset (Site L) :=
  let s := start % L
  Finset.univ.filter fun p =>
    (s ≤ p.2.val ∧ p.2.val < s + width) ∨
      p.2.val + L < s + width
def HasOpenRowIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ openHorizontalInterval L start width
def HasPeriodicRowIntervalGeneratorSupport
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := Site L) (κ := κ))
    (r : Nat) : Prop :=
  ∀ j, ∃ start width, width ≤ r ∧
    support (H.generators j) ⊆ periodicHorizontalInterval L start width
def movingFrontier
    (L stripStart stripWidth cursor r : Nat) : Finset (Site L) :=
  (openVerticalInterval L stripStart stripWidth).filter fun p =>
    p.2.val ≤ cursor ∧ cursor < p.2.val + r
def seamFrontier
    (L stripStart stripWidth r : Nat) : Finset (Site L) :=
  (openVerticalInterval L stripStart stripWidth).filter fun p =>
    p.2.val < r
end StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]
end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC
namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]
end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC


