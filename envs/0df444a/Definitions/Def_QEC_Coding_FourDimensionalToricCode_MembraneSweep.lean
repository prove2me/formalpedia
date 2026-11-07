-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
-- name    : QEC_Coding_FourDimensionalToricCode_MembraneSweep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:24:24.294035+00:00
-- url     : https://prove2.me/theorems/ed6e332c-cf76-4fc7-9706-1314da6949ef
-- title:
--   Membrane Sweep
-- statement:
--   Definitions and structural lemmas for Membrane Sweep, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_nil
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_append_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_empty
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_reverse
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_singleton
import Theorems.Thm_QEC_Coding_PauliErrorPath_endpoint_take
import Theorems.Thm_QEC_Coding_PauliErrorPath_reverse_increments
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_stateAt_zero
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_getLast_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_head_eq_some
import Theorems.Thm_QEC_Coding_PauliErrorPath_states_length
import Theorems.Thm_QEC_Coding_PauliErrorPath_take_increments
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_code
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_generators
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_term
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_cons_cons
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_nil
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_singleton
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_length_rowMajorExactPath_increments
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_movingFrontier_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openHorizontalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicHorizontalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_periodicVerticalInterval_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_rowMajorPrefix_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_seamFrontier_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_take_rowMajorSites_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorExactPath_endpoint
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
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_code
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_term
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_cons_cons
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_nil
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_singleton
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.length_rowMajorExactPath_increments
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_movingFrontier_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openHorizontalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicHorizontalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_periodicVerticalInterval_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_rowMajorPrefix_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_seamFrontier_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorExactPath_endpoint
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
namespace QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]
abbrev SweepSite (L : Nat) :=
  StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.Site L
def primalSweepPlaquette (z w : ZMod L) (p : SweepSite L) : Plaquette L :=
  (coord4 (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) z w, .xy)
def dualSweepPlaquette (x y : ZMod L) (p : SweepSite L) : Plaquette L :=
  (coord4 x y (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2), .xy)
theorem primalSweepPlaquette_injective (z w : ZMod L) :
    Function.Injective (primalSweepPlaquette z w) := by
  intro p q hpq
  have hcoord :
      coord4 (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) z w =
        coord4 (ZMod.finEquiv L q.1) (ZMod.finEquiv L q.2) z w :=
    congrArg Prod.fst hpq
  have hparts := (coord4_eq_coord4_iff _ _ _ _ _ _ _ _).mp hcoord
  exact Prod.ext
    ((ZMod.finEquiv L).injective hparts.1)
    ((ZMod.finEquiv L).injective hparts.2.1)
theorem dualSweepPlaquette_injective (x y : ZMod L) :
    Function.Injective (dualSweepPlaquette x y) := by
  intro p q hpq
  have hcoord :
      coord4 x y (ZMod.finEquiv L p.1) (ZMod.finEquiv L p.2) =
        coord4 x y (ZMod.finEquiv L q.1) (ZMod.finEquiv L q.2) :=
    congrArg Prod.fst hpq
  have hparts := (coord4_eq_coord4_iff _ _ _ _ _ _ _ _).mp hcoord
  exact Prod.ext
    ((ZMod.finEquiv L).injective hparts.2.2.1)
    ((ZMod.finEquiv L).injective hparts.2.2.2)
def primalSweepPlaquettes (z w : ZMod L) : List (Plaquette L) :=
  (StripGeometry.rowMajorSites L).map (primalSweepPlaquette z w)
def dualSweepPlaquettes (x y : ZMod L) : List (Plaquette L) :=
  (StripGeometry.rowMajorSites L).map (dualSweepPlaquette x y)
@[simp] theorem length_primalSweepPlaquettes (z w : ZMod L) :
    (primalSweepPlaquettes z w).length = L * L := by
  simp [primalSweepPlaquettes]
@[simp] theorem length_dualSweepPlaquettes (x y : ZMod L) :
    (dualSweepPlaquettes x y).length = L * L := by
  simp [dualSweepPlaquettes]
theorem primalSweepPlaquettes_nodup (z w : ZMod L) :
    (primalSweepPlaquettes z w).Nodup := by
  exact (StripGeometry.rowMajorSites_nodup L).map
    (primalSweepPlaquette_injective z w)
theorem dualSweepPlaquettes_nodup (x y : ZMod L) :
    (dualSweepPlaquettes x y).Nodup := by
  exact (StripGeometry.rowMajorSites_nodup L).map
    (dualSweepPlaquette_injective x y)
@[simp] theorem mem_primalSweepPlaquettes_toFinset
    (z w : ZMod L) (q : Plaquette L) :
    q ∈ (primalSweepPlaquettes z w).toFinset ↔
      q.2 = .xy ∧ q.1 .z = z ∧ q.1 .w = w := by
  constructor
  · intro hq
    rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨p, hp, rfl⟩
    simp [primalSweepPlaquette]
  · rintro ⟨hplane, hz, hw⟩
    let p : SweepSite L :=
      ((ZMod.finEquiv L).symm (q.1 .x), (ZMod.finEquiv L).symm (q.1 .y))
    have hp : p ∈ StripGeometry.rowMajorSites L := by
      rw [← List.mem_toFinset, StripGeometry.rowMajorSites_toFinset]
      simp
    rw [List.mem_toFinset, primalSweepPlaquettes, List.mem_map]
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · ext a
      cases a <;>
        simp [primalSweepPlaquette, p, hz, hw]
    · exact hplane.symm
@[simp] theorem mem_dualSweepPlaquettes_toFinset
    (x y : ZMod L) (q : Plaquette L) :
    q ∈ (dualSweepPlaquettes x y).toFinset ↔
      q.2 = .xy ∧ q.1 .x = x ∧ q.1 .y = y := by
  constructor
  · intro hq
    rcases List.mem_map.mp (List.mem_toFinset.mp hq) with ⟨p, hp, rfl⟩
    simp [dualSweepPlaquette]
  · rintro ⟨hplane, hx, hy⟩
    let p : SweepSite L :=
      ((ZMod.finEquiv L).symm (q.1 .z), (ZMod.finEquiv L).symm (q.1 .w))
    have hp : p ∈ StripGeometry.rowMajorSites L := by
      rw [← List.mem_toFinset, StripGeometry.rowMajorSites_toFinset]
      simp
    rw [List.mem_toFinset, dualSweepPlaquettes, List.mem_map]
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · ext a
      cases a <;>
        simp [dualSweepPlaquette, p, hx, hy]
    · exact hplane.symm
def primalSweepRegion (z w : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  ((primalSweepPlaquettes z w).take n).toFinset
def dualSweepRegion (x y : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  ((dualSweepPlaquettes x y).take n).toFinset
def primalSweepPrefix (z w : ZMod L) (n : Nat) :
    Word (ZMod 2) (Plaquette L) :=
  fun q => if q ∈ primalSweepRegion z w n then 1 else 0
def dualSweepPrefix (x y : ZMod L) (n : Nat) :
    Word (ZMod 2) (Plaquette L) :=
  fun q => if q ∈ dualSweepRegion x y n then 1 else 0
@[simp] theorem primalSweepPlaquette_mem_sweepRegion_iff
    (z w : ZMod L) (p : SweepSite L) (n : Nat) :
    primalSweepPlaquette z w p ∈ primalSweepRegion z w n ↔
      StripGeometry.rowMajorIndex p < min n (L * L) := by
  rw [primalSweepRegion, List.mem_toFinset, primalSweepPlaquettes,
    ← List.map_take, List.mem_map]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hqp : q = p :=
      (primalSweepPlaquette_injective z w) hpq
    subst q
    exact (StripGeometry.mem_take_rowMajorSites_iff p).1 hq
  · intro hp
    exact ⟨p, (StripGeometry.mem_take_rowMajorSites_iff p).2 hp, rfl⟩
@[simp] theorem dualSweepPlaquette_mem_sweepRegion_iff
    (x y : ZMod L) (p : SweepSite L) (n : Nat) :
    dualSweepPlaquette x y p ∈ dualSweepRegion x y n ↔
      StripGeometry.rowMajorIndex p < min n (L * L) := by
  rw [dualSweepRegion, List.mem_toFinset, dualSweepPlaquettes,
    ← List.map_take, List.mem_map]
  constructor
  · rintro ⟨q, hq, hpq⟩
    have hqp : q = p :=
      (dualSweepPlaquette_injective x y) hpq
    subst q
    exact (StripGeometry.mem_take_rowMajorSites_iff p).1 hq
  · intro hp
    exact ⟨p, (StripGeometry.mem_take_rowMajorSites_iff p).2 hp, rfl⟩
def sweepSiteFrontier (L n : Nat) : Finset (SweepSite L) :=
  StripGeometry.movingFrontier L 0 L (n / L) 2 ∪
    StripGeometry.seamFrontier L 0 L 2
def primalSweepFrontier (z w : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  (sweepSiteFrontier L n).image (primalSweepPlaquette z w)
def dualSweepFrontier (x y : ZMod L) (n : Nat) : Finset (Plaquette L) :=
  (sweepSiteFrontier L n).image (dualSweepPlaquette x y)
def completeSiteOrder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sites : List ι) : List ι :=
  sites ++ (Finset.univ \ sites.toFinset).toList
theorem completeSiteOrder_nodup
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {sites : List ι} (hnodup : sites.Nodup) :
    (completeSiteOrder sites).Nodup := by
  rw [completeSiteOrder, List.nodup_append']
  refine ⟨hnodup, (Finset.univ \ sites.toFinset).nodup_toList, ?_⟩
  rw [List.disjoint_left]
  intro q hqSites hqRest
  have hqMem : q ∈ Finset.univ \ sites.toFinset := by
    simpa using hqRest
  exact (Finset.mem_sdiff.mp hqMem).2 (by simpa using hqSites)
theorem completeSiteOrder_toFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sites : List ι) :
    (completeSiteOrder sites).toFinset = Finset.univ := by
  ext q
  simp [completeSiteOrder]
def primalSweepOrder (z w : ZMod L) : List (Plaquette L) :=
  completeSiteOrder (primalSweepPlaquettes z w)
def dualSweepOrder (x y : ZMod L) : List (Plaquette L) :=
  completeSiteOrder (dualSweepPlaquettes x y)
theorem primalSweepOrder_nodup (z w : ZMod L) :
    (primalSweepOrder z w).Nodup :=
  completeSiteOrder_nodup (primalSweepPlaquettes_nodup z w)
theorem dualSweepOrder_nodup (x y : ZMod L) :
    (dualSweepOrder x y).Nodup :=
  completeSiteOrder_nodup (dualSweepPlaquettes_nodup x y)
@[simp] theorem primalSweepOrder_toFinset (z w : ZMod L) :
    (primalSweepOrder z w).toFinset = Finset.univ :=
  completeSiteOrder_toFinset _
@[simp] theorem dualSweepOrder_toFinset (x y : ZMod L) :
    (dualSweepOrder x y).toFinset = Finset.univ :=
  completeSiteOrder_toFinset _
def primalMembraneSweepPath (z w : ZMod L) :
    PauliErrorPath (ι := Plaquette L) :=
  PauliErrorPath.orderedExact (primalMembraneError (primalXYMembrane z w))
    (primalSweepOrder z w) (primalSweepOrder_nodup z w)
    (primalSweepOrder_toFinset z w)
def dualMembraneSweepPath (x y : ZMod L) :
    PauliErrorPath (ι := Plaquette L) :=
  PauliErrorPath.orderedExact (dualMembraneError (dualXYMembrane x y))
    (dualSweepOrder x y) (dualSweepOrder_nodup x y)
    (dualSweepOrder_toFinset x y)
end QEC.Coding.PeriodicCubical4


