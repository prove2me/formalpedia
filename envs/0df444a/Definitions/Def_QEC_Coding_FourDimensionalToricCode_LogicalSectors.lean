-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
-- name    : QEC_Coding_FourDimensionalToricCode_LogicalSectors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:09:15.273444+00:00
-- url     : https://prove2.me/theorems/73ea9838-e8ac-4b72-adf5-80e8d11ba6db
-- title:
--   Logical Sectors
-- statement:
--   Definitions and structural lemmas for Logical Sectors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/LogicalSectors.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_code
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_generators
import Theorems.Thm_QEC_Coding_PeriodicCubical4_toricHamiltonian_term
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_code
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_generators
attribute [local simp] QEC.Coding.PeriodicCubical4.toricHamiltonian_term
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
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
theorem sum_add_one {L : Nat} [NeZero L] {M : Type*} [AddCommMonoid M]
    (f : ZMod L → M) :
    (∑ a : ZMod L, f (a + 1)) = ∑ a : ZMod L, f a :=
  Equiv.sum_comp (Equiv.addRight 1) f
def coord4 {L : Nat} (x y z w : ZMod L) : Coord L
  | .x => x
  | .y => y
  | .z => z
  | .w => w
@[simp] theorem coord4_x {L : Nat} (x y z w : ZMod L) :
    coord4 x y z w .x = x := rfl
@[simp] theorem coord4_y {L : Nat} (x y z w : ZMod L) :
    coord4 x y z w .y = y := rfl
@[simp] theorem coord4_z {L : Nat} (x y z w : ZMod L) :
    coord4 x y z w .z = z := rfl
@[simp] theorem coord4_w {L : Nat} (x y z w : ZMod L) :
    coord4 x y z w .w = w := rfl
@[simp] theorem coord4_eq_coord4_iff {L : Nat}
    (x y z w x' y' z' w' : ZMod L) :
    coord4 x y z w = coord4 x' y' z' w' ↔
      x = x' ∧ y = y' ∧ z = z' ∧ w = w' := by
  constructor
  · intro h
    exact ⟨congrFun h .x, congrFun h .y, congrFun h .z, congrFun h .w⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl
def primalXYMembrane {L : Nat} [NeZero L] (z w : ZMod L) :
    Word (ZMod 2) (Plaquette L) :=
  ∑ x : ZMod L, ∑ y : ZMod L, cellWord (coord4 x y z w, .xy)
def dualXYMembrane {L : Nat} [NeZero L] (x y : ZMod L) :
    Word (ZMod 2) (Plaquette L) :=
  ∑ z : ZMod L, ∑ w : ZMod L, cellWord (coord4 x y z w, .xy)
@[simp] theorem primalXYMembrane_apply_coord4 {L : Nat} [NeZero L]
    (z₀ w₀ x y z w : ZMod L) (q : Plane) :
    primalXYMembrane z₀ w₀ (coord4 x y z w, q) =
      if q = .xy ∧ z = z₀ ∧ w = w₀ then 1 else 0 := by
  classical
  by_cases hq : q = .xy
  · subst q
    by_cases hz : z = z₀
    · subst z
      by_cases hw : w = w₀
      · subst w
        simp only [primalXYMembrane, Finset.sum_apply]
        rw [Fintype.sum_eq_single x]
        · rw [Fintype.sum_eq_single y]
          · simp [cellWord]
          · intro b hby
            simp [cellWord, Prod.ext_iff, hby]
        · intro a hax
          apply Fintype.sum_eq_zero
          intro b
          simp [cellWord, Prod.ext_iff, hax]
      · simp [primalXYMembrane, cellWord, Prod.ext_iff, hw]
    · simp [primalXYMembrane, cellWord, Prod.ext_iff, hz]
  · simp [primalXYMembrane, cellWord, Prod.ext_iff, hq]
@[simp] theorem dualXYMembrane_apply_coord4 {L : Nat} [NeZero L]
    (x₀ y₀ x y z w : ZMod L) (q : Plane) :
    dualXYMembrane x₀ y₀ (coord4 x y z w, q) =
      if q = .xy ∧ x = x₀ ∧ y = y₀ then 1 else 0 := by
  classical
  by_cases hq : q = .xy
  · subst q
    by_cases hx : x = x₀
    · subst x
      by_cases hy : y = y₀
      · subst y
        simp only [dualXYMembrane, Finset.sum_apply]
        rw [Fintype.sum_eq_single z]
        · rw [Fintype.sum_eq_single w]
          · simp [cellWord]
          · intro b hbw
            simp [cellWord, Prod.ext_iff, hbw]
        · intro a haz
          apply Fintype.sum_eq_zero
          intro b
          simp [cellWord, Prod.ext_iff, haz]
      · simp [dualXYMembrane, cellWord, Prod.ext_iff, hy]
    · simp [dualXYMembrane, cellWord, Prod.ext_iff, hx]
  · simp [dualXYMembrane, cellWord, Prod.ext_iff, hq]
theorem shift_coord4_x {L : Nat} (x y z w : ZMod L) :
    shift (coord4 x y z w) .x = coord4 (x + 1) y z w := by
  ext a
  cases a <;> simp [shift, coord4]
theorem shift_coord4_y {L : Nat} (x y z w : ZMod L) :
    shift (coord4 x y z w) .y = coord4 x (y + 1) z w := by
  ext a
  cases a <;> simp [shift, coord4]
theorem shift_coord4_z {L : Nat} (x y z w : ZMod L) :
    shift (coord4 x y z w) .z = coord4 x y (z + 1) w := by
  ext a
  cases a <;> simp [shift, coord4]
theorem shift_coord4_w {L : Nat} (x y z w : ZMod L) :
    shift (coord4 x y z w) .w = coord4 x y z (w + 1) := by
  ext a
  cases a <;> simp [shift, coord4]
theorem coord4_eta {L : Nat} (c : Coord L) :
    coord4 (c .x) (c .y) (c .z) (c .w) = c := by
  ext a
  cases a <;> rfl
@[simp] theorem wordPairing_cellWord_right {L : Nat} [NeZero L]
    (m : Word (ZMod 2) (Plaquette L)) (p : Plaquette L) :
    wordPairing m (cellWord p) = m p := by
  classical
  simp only [wordPairing_apply, dotProduct, cellWord]
  rw [Fintype.sum_eq_single p]
  · simp
  · intro q hqp
    simp [hqp]
theorem boundary2_primalXYMembrane {L : Nat} [NeZero L] (z w : ZMod L) :
    boundary2 (primalXYMembrane z w) = 0 := by
  simp only [primalXYMembrane, map_sum, boundary2, linearize_cellWord,
    plaquetteBoundary, shift_coord4_x, shift_coord4_y,
    Finset.sum_add_distrib]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 x (y + 1) z w, Axis.x)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Axis.x) by
      apply Fintype.sum_congr
      intro x
      exact sum_add_one (M := Word (ZMod 2) (Link L))
        (fun y : ZMod L => cellWord (coord4 x y z w, Axis.x))]
  rw [show (∑ x : ZMod L, ∑ y : ZMod L,
      cellWord (coord4 (x + 1) y z w, Axis.y)) =
      ∑ x : ZMod L, ∑ y : ZMod L,
        cellWord (coord4 x y z w, Axis.y) by
      exact sum_add_one (M := Word (ZMod 2) (Link L))
        (fun x : ZMod L => ∑ y : ZMod L,
          cellWord (coord4 x y z w, Axis.y))]
  simp
theorem wordPairing_dualXYMembrane_cubeBoundary {L : Nat} [NeZero L]
    (x y : ZMod L) (c : Cube L) :
    wordPairing (dualXYMembrane x y) (cubeBoundary c) = 0 := by
  rcases c with ⟨c, v⟩
  rw [← coord4_eta c]
  cases v <;>
    simp only [cubeBoundary, map_add, wordPairing_cellWord_right,
      shift_coord4_x, shift_coord4_y, shift_coord4_z, shift_coord4_w,
      dualXYMembrane_apply_coord4] <;>
    split_ifs <;> simp_all <;> exact ZModModule.add_self 1
theorem transpose_boundary3_dualXYMembrane {L : Nat} [NeZero L]
    (x y : ZMod L) :
    wordLinearMapTranspose boundary3 (dualXYMembrane x y) = 0 := by
  apply (wordPairing_nondegenerate (F := ZMod 2)).left
  intro c
  rw [wordPairing_wordLinearMapTranspose]
  rw [← word_eq_sum_single (F := ZMod 2) c]
  simp only [map_sum, boundary3, linearize_single, map_smul]
  change (∑ a : Cube L, c a *
    wordPairing (dualXYMembrane x y) (cubeBoundary a)) = 0
  simp only [wordPairing_dualXYMembrane_cubeBoundary, mul_zero,
    Finset.sum_const_zero]
theorem primalXYMembrane_mem_middleCycleCode {L : Nat} [NeZero L]
    (z w : ZMod L) :
    primalXYMembrane z w ∈
      (plaquetteChainComplex (L := L)).middleCycleCode.carrier := by
  rw [ChainComplexData.mem_middleCycleCode_iff]
  exact boundary2_primalXYMembrane z w
theorem dualXYMembrane_mem_middleCocycleCode {L : Nat} [NeZero L]
    (x y : ZMod L) :
    dualXYMembrane x y ∈
      (plaquetteChainComplex (L := L)).middleCocycleCode.carrier := by
  rw [ChainComplexData.mem_middleCocycleCode_iff]
  exact transpose_boundary3_dualXYMembrane x y
def primalXYCycle {L : Nat} [NeZero L] (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).middleCycleCode.carrier :=
  ⟨primalXYMembrane z w, primalXYMembrane_mem_middleCycleCode z w⟩
noncomputable def primalXYHomologyClass {L : Nat} [NeZero L] (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).middleHomology :=
  Submodule.Quotient.mk (primalXYCycle z w)
def dualXYCocycle {L : Nat} [NeZero L] (x y : ZMod L) :
    (plaquetteChainComplex (L := L)).middleCocycleCode.carrier :=
  ⟨dualXYMembrane x y, dualXYMembrane_mem_middleCocycleCode x y⟩
noncomputable def dualXYCohomologyClass {L : Nat} [NeZero L] (x y : ZMod L) :
    (plaquetteChainComplex (L := L)).middleCohomology :=
  Submodule.Quotient.mk (dualXYCocycle x y)
def primalXYPureZRepresentative {L : Nat} [NeZero L] (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode.dual.carrier :=
  ⟨primalXYMembrane z w, by
    rw [(plaquetteChainComplex (L := L)).firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    exact primalXYMembrane_mem_middleCycleCode z w⟩
noncomputable def primalXYPureZLogicalClass {L : Nat} [NeZero L] (z w : ZMod L) :
    (plaquetteChainComplex (L := L)).pureZLogicalQuotient :=
  Submodule.Quotient.mk (primalXYPureZRepresentative z w)
def dualXYPureXRepresentative {L : Nat} [NeZero L] (x y : ZMod L) :
    (plaquetteChainComplex (L := L)).middleBoundaryCode.dual.carrier :=
  ⟨dualXYMembrane x y, by
    rw [(plaquetteChainComplex (L := L)).middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
    exact dualXYMembrane_mem_middleCocycleCode x y⟩
noncomputable def dualXYPureXLogicalClass {L : Nat} [NeZero L] (x y : ZMod L) :
    (plaquetteChainComplex (L := L)).pureXLogicalQuotient :=
  Submodule.Quotient.mk (dualXYPureXRepresentative x y)
open PauliSymplectic
noncomputable def primalZLogical {L : Nat} [NeZero L] (z w : ZMod L) :
    Binary (Plaquette L) :=
  cssZCheck (primalXYMembrane z w)
noncomputable def dualXLogical {L : Nat} [NeZero L] (x y : ZMod L) :
    Binary (Plaquette L) :=
  cssXCheck (dualXYMembrane x y)
end QEC.Coding.PeriodicCubical4


