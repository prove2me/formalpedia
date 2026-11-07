-- Prove2me | Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
-- name    : QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:57:29.527202+00:00
-- url     : https://prove2.me/theorems/6238b23d-ac2d-4714-84dc-a668a370239b
-- title:
--   Large Distance Separator
-- statement:
--   Definitions and structural lemmas for Large Distance Separator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
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
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
noncomputable def daiLiLargeDistanceThreshold (d n : Nat) : ℝ :=
  (d : ℝ) / (200 * Real.sqrt (n : ℝ))
def DaiLiLargeDistanceFewLongInteractions
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat) : Prop :=
  200 * P.longInteractionCount embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι)) ≤ d
def daiLiSingletonSubsystem (q : ι) : FiniteSubsystem ι :=
  ⟨{q}⟩
def daiLiFiniteSubsystem (vertices : Finset ι) : FiniteSubsystem ι :=
  ⟨vertices⟩
def daiLiTenthCount (region : Finset ι) : Nat :=
  (region.card + 9) / 10
def daiLiCoordinateSupport (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  region.image coordinate
def daiLiLowerTenthCandidates (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  (daiLiCoordinateSupport region coordinate).filter fun cut =>
    daiLiTenthCount region ≤ (region.filter fun q => coordinate q ≤ cut).card
omit [Fintype ι] [DecidableEq ι] in
/-- The lower-tenth candidate set is nonempty for every nonempty finite
region: its maximum occupied coordinate is a concrete candidate. -/
theorem daiLiLowerTenthCandidates_nonempty
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (daiLiLowerTenthCandidates region coordinate).Nonempty := by
  classical
  let support := daiLiCoordinateSupport region coordinate
  have hSupport : support.Nonempty := by
    simpa [support, daiLiCoordinateSupport] using hRegion.image coordinate
  let high := support.max' hSupport
  refine ⟨high, Finset.mem_filter.mpr ⟨Finset.max'_mem support hSupport, ?_⟩⟩
  have hAll : region.filter (fun q => coordinate q ≤ high) = region := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    change coordinate q ≤ support.max' hSupport
    apply Finset.le_max'
    simpa [support, daiLiCoordinateSupport] using
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩ : coordinate q ∈ region.image coordinate)
  rw [hAll]
  change (region.card + 9) / 10 ≤ region.card
  omega
noncomputable def daiLiLowerTenthCoordinate
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) : ℝ :=
  (daiLiLowerTenthCandidates region coordinate).min'
    (daiLiLowerTenthCandidates_nonempty region coordinate hRegion)
def daiLiUpperTenthCandidates (region : Finset ι) (coordinate : ι → ℝ) : Finset ℝ :=
  (daiLiCoordinateSupport region coordinate).filter fun cut =>
    daiLiTenthCount region ≤ (region.filter fun q => cut ≤ coordinate q).card
omit [Fintype ι] [DecidableEq ι] in
/-- The upper-tenth candidate set is nonempty: its minimum occupied coordinate
is a concrete candidate. -/
theorem daiLiUpperTenthCandidates_nonempty
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    (daiLiUpperTenthCandidates region coordinate).Nonempty := by
  classical
  let support := daiLiCoordinateSupport region coordinate
  have hSupport : support.Nonempty := by
    simpa [support, daiLiCoordinateSupport] using hRegion.image coordinate
  let low := support.min' hSupport
  refine ⟨low, Finset.mem_filter.mpr ⟨Finset.min'_mem support hSupport, ?_⟩⟩
  have hAll : region.filter (fun q => low ≤ coordinate q) = region := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    change support.min' hSupport ≤ coordinate q
    apply Finset.min'_le
    simpa [support, daiLiCoordinateSupport] using
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩ : coordinate q ∈ region.image coordinate)
  rw [hAll]
  change (region.card + 9) / 10 ≤ region.card
  omega
noncomputable def daiLiUpperTenthCoordinate
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) : ℝ :=
  (daiLiUpperTenthCandidates region coordinate).max'
    (daiLiUpperTenthCandidates_nonempty region coordinate hRegion)
noncomputable def daiLiTenthCore
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : Finset ι :=
  region.filter fun q =>
    daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion ≤
        (embedding.point q).1 ∧
      (embedding.point q).1 ≤
        daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion ∧
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion ≤
        (embedding.point q).2 ∧
      (embedding.point q).2 ≤
        daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion
noncomputable def daiLiTenthExterior
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : Finset ι :=
  (region.filter fun q => (embedding.point q).1 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
    (region.filter fun q =>
      daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
        (embedding.point q).1) ∪
    (region.filter fun q => (embedding.point q).2 <
      daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion) ∪
    (region.filter fun q =>
      daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
        (embedding.point q).2)
noncomputable def daiLiTenthCoreLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : ℝ × ℝ :=
  (daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion,
    daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion)
noncomputable def daiLiTenthCoreUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) : ℝ × ℝ :=
  (daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion,
    daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion)
def daiLiVerticalEqualBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lower upper : ℝ) (m : Nat) (i : Fin m) : Finset ι :=
  region.filter fun q =>
    lower + (i : ℝ) * ((upper - lower) / m) ≤ (embedding.point q).1 ∧
      (embedding.point q).1 < lower + ((i : ℝ) + 1) * ((upper - lower) / m)
noncomputable def daiLiSeparatorBandCount (ell : ℝ) (n : Nat) : Nat :=
  Nat.floor (Real.sqrt n / (8 * ell)) + 1
def daiLiVerticalBandLower (lower upper : ℝ) (m : Nat) (i : Fin m) : ℝ :=
  lower + (i : ℝ) * ((upper - lower) / m)
def daiLiVerticalBandUpper (lower upper : ℝ) (m : Nat) (i : Fin m) : ℝ :=
  lower + ((i : ℝ) + 1) * ((upper - lower) / m)
def daiLiHorizontalEqualBand
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lower upper : ℝ) (m : Nat) (i : Fin m) : Finset ι :=
  region.filter fun q =>
    lower + (i : ℝ) * ((upper - lower) / m) ≤ (embedding.point q).2 ∧
      (embedding.point q).2 < lower + ((i : ℝ) + 1) * ((upper - lower) / m)
def daiLiHorizontalSeparatorLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (lowerCut : ℝ) : Finset ι :=
  region.filter fun q => (embedding.point q).2 < lowerCut
def daiLiHorizontalSeparatorStrip
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Finset ι :=
  region.filter fun q => lowerCut < (embedding.point q).2 ∧ (embedding.point q).2 < upperCut
def daiLiHorizontalSeparatorUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (upperCut : ℝ) : Finset ι :=
  region.filter fun q => upperCut < (embedding.point q).2
def DaiLiHorizontalCutsAvoid
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Prop :=
  ∀ q ∈ region,
    (embedding.point q).2 ≠ lowerCut ∧ (embedding.point q).2 ≠ upperCut
def daiLiVerticalSeparatorLower
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (lowerCut : ℝ) : Finset ι :=
  region.filter fun q => (embedding.point q).1 < lowerCut
def daiLiVerticalSeparatorStrip
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Finset ι :=
  region.filter fun q => lowerCut < (embedding.point q).1 ∧ (embedding.point q).1 < upperCut
def daiLiVerticalSeparatorUpper
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι) (upperCut : ℝ) : Finset ι :=
  region.filter fun q => upperCut < (embedding.point q).1
def DaiLiVerticalCutsAvoid
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (lowerCut upperCut : ℝ) : Prop :=
  ∀ q ∈ region,
    (embedding.point q).1 ≠ lowerCut ∧ (embedding.point q).1 ≠ upperCut
noncomputable def daiLiRecursivePotential (ell : ℝ) (root region : Nat) : ℝ :=
  160 * ell * (Real.sqrt root - Real.sqrt region)
noncomputable def daiLiGoodExteriorNeighbors
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) : Finset ι :=
  by
    classical
    exact (Finset.univ \ region).filter fun q =>
      ∃ p : ι, p ∈ region ∧ P.fixedGeneratorInteraction p q ∧
        embedding.distance p q < ell
def daiLiRecursiveGoodPart
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (ell : ℝ) (region : Finset ι) : Finset ι :=
  region \ longInteractionEndpointQubits P embedding ell
end QEC.Locality


