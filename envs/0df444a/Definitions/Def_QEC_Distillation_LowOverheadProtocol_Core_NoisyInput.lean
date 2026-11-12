-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
-- name    : QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:28:14.299886+00:00
-- url     : https://prove2.me/theorems/7348e7f6-e34e-40a2-ae72-2dc1c1d6d5a4
-- title:
--   Noisy Input
-- statement:
--   Definitions and structural lemmas for Noisy Input, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
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
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_square
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
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
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
noncomputable section
namespace QEC
namespace Distillation
namespace HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u
abbrev DiagonalErrorRate := Set.Icc (0 : Real) (1 / 2)
abbrev PhysicalErrorWord (m w : Nat) :=
  Word (ZMod 2) (HH18PuncturedReedMuller.PhysicalSite m w)
def bitErrorWeight (epsilon : DiagonalErrorRate) (error : ZMod 2) : Real :=
  if error = 0 then 1 - epsilon.1 else epsilon.1
theorem bitErrorWeight_nonneg (epsilon : DiagonalErrorRate) (error : ZMod 2) :
    0 <= bitErrorWeight epsilon error := by
  unfold bitErrorWeight
  split_ifs
  · linarith [epsilon.property.2]
  · exact epsilon.property.1
theorem sum_binary (f : ZMod 2 -> Real) :
    (∑ bit, f bit) = f 0 + f 1 := by
  calc
    (∑ bit : ZMod 2, f bit) =
        ∑ index : Fin 2, f (ZMod.finEquiv 2 index) := by
      exact Fintype.sum_equiv (ZMod.finEquiv 2).toEquiv.symm _ _ (fun _ => rfl)
    _ = f 0 + f 1 := by
      rw [Fin.sum_univ_two]
      norm_num
theorem bitErrorWeight_sum (epsilon : DiagonalErrorRate) :
    ∑ error : ZMod 2, bitErrorWeight epsilon error = 1 := by
  rw [sum_binary]
  simp [bitErrorWeight]
def idealTInvResourceState : QubitSpace :=
  OneQubitMagic.phaseState (-Real.pi / 4)
theorem idealTInvResourceState_ne_zero : idealTInvResourceState ≠ 0 := by
  simpa [idealTInvResourceState] using
    OneQubitMagic.phaseState_ne_zero (-Real.pi / 4)
def tInvResourceErrorState (error : ZMod 2) : QubitSpace :=
  if error = 0 then idealTInvResourceState else pauliZ idealTInvResourceState
theorem tInvResourceErrorState_ne_zero (error : ZMod 2) :
    tInvResourceErrorState error ≠ 0 := by
  by_cases herror : error = 0
  · simpa [tInvResourceErrorState, herror] using idealTInvResourceState_ne_zero
  · intro hzero
    have hflipped : pauliZ idealTInvResourceState = 0 := by
      simpa [tInvResourceErrorState, herror] using hzero
    have hrecover : pauliZ (pauliZ idealTInvResourceState) =
        idealTInvResourceState := by
      simpa only [Module.End.mul_apply, Module.End.one_apply] using
        LinearMap.congr_fun pauliZ_square idealTInvResourceState
    rw [hflipped] at hrecover
    simp only [map_zero] at hrecover
    exact idealTInvResourceState_ne_zero hrecover.symm
noncomputable def tInvResourceErrorDensity (error : ZMod 2) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (tInvResourceErrorState error) (tInvResourceErrorState_ne_zero error)
@[simp]
theorem tInvResourceErrorDensity_zero :
    tInvResourceErrorDensity 0 = OneQubitMagic.phaseStateDensity (-Real.pi / 4) := by
  rfl
noncomputable def noisyTInvResource (epsilon : DiagonalErrorRate) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ
    (bitErrorWeight epsilon) tInvResourceErrorDensity
    (by
      intro error _herror
      exact bitErrorWeight_nonneg epsilon error)
    (by simpa using bitErrorWeight_sum epsilon)
noncomputable def noisyTInvResources (count : Nat) (epsilon : DiagonalErrorRate) :
    ResourceInput count QubitSpace :=
  fun _ => noisyTInvResource epsilon
def idealTInvResourceRegister {ι : Type u} [Fintype ι] : QubitRegister ι :=
  WithLp.toLp 2 fun bits => ∏ i, idealTInvResourceState (bits i)
theorem idealTInvResourceRegister_ne_zero {ι : Type u} [Fintype ι] :
    idealTInvResourceRegister (ι := ι) ≠ 0 := by
  classical
  have hzero : idealTInvResourceState 0 ≠ 0 := by
    rw [idealTInvResourceState, OneQubitMagic.phaseState_apply_zero]
    have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    exact inv_ne_zero hsqrt_ne
  have hproduct : (∏ _i : ι, idealTInvResourceState 0) ≠ 0 := by
    simp [hzero]
  intro hzero
  have hcoordinate :=
    congrArg (fun psi : QubitRegister ι => psi (fun _ => 0)) hzero
  apply hproduct
  simpa [idealTInvResourceRegister] using hcoordinate
def zErrorOperator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : Operator (QubitRegister ι) :=
  PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)
def errorWordState {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : QubitRegister ι :=
  zErrorOperator error (idealTInvResourceRegister (ι := ι))
theorem errorWordState_ne_zero {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : errorWordState error ≠ 0 := by
  intro hzero
  have hrecover := LinearMap.congr_fun
    (PauliSymplectic.toQubitOperator_adjoint_comp_self
      (PauliSymplectic.cssZCheck error))
    (idealTInvResourceRegister (ι := ι))
  simp only [LinearMap.comp_apply, Module.End.one_apply] at hrecover
  have happlied :
      PauliSymplectic.toQubitOperator (PauliSymplectic.cssZCheck error)
          (idealTInvResourceRegister (ι := ι)) = 0 := by
    simpa [errorWordState, zErrorOperator] using hzero
  rw [happlied] at hrecover
  simp only [map_zero] at hrecover
  exact idealTInvResourceRegister_ne_zero hrecover.symm
noncomputable def errorWordDensity {ι : Type u} [Fintype ι] [DecidableEq ι]
    (error : Word (ZMod 2) ι) : DensityOperator (QubitRegister ι) :=
  DensityOperator.pureOfNonzero
    (errorWordState error) (errorWordState_ne_zero error)
def errorWordWeight {ι : Type u} [Fintype ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) : Real :=
  ∏ i, bitErrorWeight epsilon (error i)
theorem errorWordWeight_nonneg {ι : Type u} [Fintype ι]
    (epsilon : DiagonalErrorRate) (error : Word (ZMod 2) ι) :
    0 <= errorWordWeight epsilon error := by
  classical
  unfold errorWordWeight
  apply Finset.prod_nonneg
  intro i _hi
  exact bitErrorWeight_nonneg epsilon (error i)
theorem errorWordWeight_sum {ι : Type u} [Fintype ι] [DecidableEq ι]
    (epsilon : DiagonalErrorRate) :
    ∑ error : Word (ZMod 2) ι, errorWordWeight epsilon error = 1 := by
  classical
  unfold errorWordWeight
  rw [← Fintype.prod_sum]
  simp [bitErrorWeight_sum]
noncomputable def independentNoisyTRegister {ι : Type u}
    [Fintype ι] [DecidableEq ι] (epsilon : DiagonalErrorRate) :
    DensityOperator (QubitRegister ι) :=
  DensityOperator.convexCombination Finset.univ
    (errorWordWeight epsilon) errorWordDensity
    (by
      intro error _herror
      exact errorWordWeight_nonneg epsilon error)
    (by simpa using errorWordWeight_sum (ι := ι) epsilon)
noncomputable def hh18NoisyInput (epsilon : DiagonalErrorRate) (m w : Nat) :
    DensityOperator
      (QubitRegister (HH18PuncturedReedMuller.PhysicalSite m w)) :=
  independentNoisyTRegister epsilon
theorem hh18_15_1_0_admissible : Admissible 0 1 4 := by
  norm_num [Admissible]
noncomputable def hh18_15_1_0_noisyInput (epsilon : DiagonalErrorRate) :
    DensityOperator
      (QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0)) :=
  hh18NoisyInput epsilon 4 0
noncomputable def hh18_15_1_0_encodedCode :=
  HH18PuncturedReedMuller.encodedCode hh18_15_1_0_admissible
noncomputable def hh18LogicalPlusInput :
    QubitRegister (HH18PuncturedReedMuller.LogicalSite 4 0) :=
  Triorthogonal.BinaryRowFamily.logicalPlusState
    (HH18PuncturedReedMuller.LogicalSite 4 0)
noncomputable def hh18EncodedLogicalPlusInput :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  hh18_15_1_0_encodedCode.encode hh18LogicalPlusInput
noncomputable def hh18PhysicalTInvBranch :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  HH18PuncturedReedMuller.physicalTInv 0 4 hh18EncodedLogicalPlusInput
noncomputable def hh18PhysicalTInvErrorBranch
    (error : PhysicalErrorWord 4 0) :
    QubitRegister (HH18PuncturedReedMuller.PhysicalSite 4 0) :=
  zErrorOperator error hh18PhysicalTInvBranch
end HH18NoisyInput
end Distillation
end QEC


