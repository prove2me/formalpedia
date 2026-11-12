-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:59:02.729864+00:00
-- url     : https://prove2.me/theorems/8893115d-d6b3-4631-97b1-c35034aea5cf
-- title:
--   Decoder
-- statement:
--   Definitions and structural lemmas for Decoder, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Decoder.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
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
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_independentNoisyTRegister_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_logicalPlus_norm
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
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
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
attribute [local simp] QEC.Distillation.HH18NoisyInput.independentNoisyTRegister_toOperator
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
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
def ambientEncodingIsometry {w r m : Nat} (h : Admissible w r m) :
    LogicalRegister m w →ₗᵢ[Complex] PhysicalRegister m w :=
  (HH18PuncturedReedMuller.encodedCode h).code.carrier.subtypeₗᵢ.comp
    (HH18PuncturedReedMuller.encodedCode h).encoding.toLinearIsometry
@[simp] theorem ambientEncodingIsometry_apply {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    ambientEncodingIsometry h psi =
      ((HH18PuncturedReedMuller.encodedCode h).encoding psi : PhysicalRegister m w) :=
  rfl
def codeDecoderBranch {w r m : Nat} (h : Admissible w r m) :
    PhysicalRegister m w →ₗ[Complex] LogicalRegister m w :=
  LinearMap.adjoint (ambientEncodingIsometry h).toLinearMap
@[simp] theorem codeDecoderBranch_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    codeDecoderBranch h (ambientEncodingIsometry h psi) = psi := by
  change LinearMap.adjoint (ambientEncodingIsometry h).toLinearMap
    ((ambientEncodingIsometry h).toLinearMap psi) = psi
  exact LinearMap.congr_fun (ambientEncodingIsometry h).adjoint_comp_self' psi
theorem adjoint_codeDecoderBranch {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (codeDecoderBranch h) = (ambientEncodingIsometry h).toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]
def decoderCodeProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (PhysicalRegister m w) :=
  (LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)
@[simp] theorem decoderCodeProjector_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    decoderCodeProjector h (ambientEncodingIsometry h psi) = ambientEncodingIsometry h psi := by
  change LinearMap.adjoint (codeDecoderBranch h)
    (codeDecoderBranch h (ambientEncodingIsometry h psi)) = ambientEncodingIsometry h psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl
theorem codeDecoderBranch_comp_adjoint {w r m : Nat} (h : Admissible w r m) :
    (codeDecoderBranch h).comp (LinearMap.adjoint (codeDecoderBranch h)) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact (ambientEncodingIsometry h).adjoint_comp_self'
theorem decoderCodeProjector_idempotent {w r m : Nat} (h : Admissible w r m) :
    (decoderCodeProjector h).comp (decoderCodeProjector h) = decoderCodeProjector h := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)).comp
        ((LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h)) =
      (LinearMap.adjoint (codeDecoderBranch h)).comp
        (((codeDecoderBranch h).comp (LinearMap.adjoint (codeDecoderBranch h))).comp
          (codeDecoderBranch h)) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint (codeDecoderBranch h)).comp
          ((1 : Operator (LogicalRegister m w)).comp (codeDecoderBranch h)) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint (codeDecoderBranch h)).comp (codeDecoderBranch h) := by
      ext psi
      rfl
theorem decoderCodeProjector_adjoint {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (decoderCodeProjector h) = decoderCodeProjector h := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]
def decoderComplementProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (PhysicalRegister m w) :=
  1 - decoderCodeProjector h
theorem decoderComplementProjector_adjoint {w r m : Nat} (h : Admissible w r m) :
    LinearMap.adjoint (decoderComplementProjector h) = decoderComplementProjector h := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]
theorem decoderComplementProjector_idempotent {w r m : Nat} (h : Admissible w r m) :
    (decoderComplementProjector h).comp (decoderComplementProjector h) =
      decoderComplementProjector h := by
  ext psi
  have hprojector := LinearMap.congr_fun (decoderCodeProjector_idempotent h) psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp] theorem decoderComplementProjector_encoded {w r m : Nat}
    (h : Admissible w r m) (psi : LogicalRegister m w) :
    decoderComplementProjector h (ambientEncodingIsometry h psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf
noncomputable def decoderFallbackState (m w : Nat) : LogicalRegister m w :=
  EuclideanSpace.basisFun (Bitstring (LogicalSite m w)) Complex (fun _ => 0)
theorem decoderFallbackState_inner_self (m w : Nat) :
    inner Complex (decoderFallbackState m w) (decoderFallbackState m w) = 1 := by
  simp [decoderFallbackState]
theorem decoderFallbackState_normSq (m w : Nat) :
    ‖decoderFallbackState m w‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    decoderFallbackState_inner_self]
  norm_num
noncomputable def decoderPhysicalBasis (m w : Nat) :=
  stdOrthonormalBasis Complex (PhysicalRegister m w)
def complementDecoderBranch {w r m : Nat} (h : Admissible w r m)
    (i : Fin (Module.finrank Complex (PhysicalRegister m w))) :
    PhysicalRegister m w →ₗ[Complex] LogicalRegister m w :=
  (InnerProductSpace.rankOne Complex (decoderFallbackState m w)
    (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap
theorem complementDecoderBranch_adjoint_comp {w r m : Nat} (h : Admissible w r m)
    (i : Fin (Module.finrank Complex (PhysicalRegister m w))) :
    (LinearMap.adjoint (complementDecoderBranch h i)).comp (complementDecoderBranch h i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector h (decoderPhysicalBasis m w i))
        (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (decoderFallbackState m w)
        (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector h (decoderPhysicalBasis m w i))
        (decoderFallbackState m w)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex (decoderFallbackState m w)
      (decoderComplementProjector h (decoderPhysicalBasis m w i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState m w‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq m w
  simp [LinearMap.comp_apply, hnormSq]
theorem sum_complementDecoderBranch_adjoint_comp {w r m : Nat}
    (h : Admissible w r m) :
    ∑ i : Fin (Module.finrank Complex (PhysicalRegister m w)),
      (LinearMap.adjoint (complementDecoderBranch h i)).comp (complementDecoderBranch h i) =
        decoderComplementProjector h := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector h (decoderPhysicalBasis m w i))
      (decoderComplementProjector h (decoderPhysicalBasis m w i))).toLinearMap) =
      (decoderComplementProjector h).comp
        (LinearMap.adjoint (decoderComplementProjector h)) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← (decoderPhysicalBasis m w).sum_repr'
          (LinearMap.adjoint (decoderComplementProjector h) psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = (decoderComplementProjector h).comp (decoderComplementProjector h) := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector h := decoderComplementProjector_idempotent h
def decoderKrausFamily {w r m : Nat} (h : Admissible w r m) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex (PhysicalRegister m w))))
      (PhysicalRegister m w) (LogicalRegister m w) where
  operator
    | .inl _ => codeDecoderBranch h
    | .inr i => complementDecoderBranch h i
theorem decoderKrausFamily_complete {w r m : Nat} (h : Admissible w r m) :
    (decoderKrausFamily h).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector h) +
      (∑ i : Fin (Module.finrank Complex (PhysicalRegister m w)),
        (LinearMap.adjoint (complementDecoderBranch h i)).comp
          (complementDecoderBranch h i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]
noncomputable def decoderChannel {w r m : Nat} (h : Admissible w r m) :
    QuantumChannel (PhysicalRegister m w) (LogicalRegister m w) :=
  (decoderKrausFamily h).toQuantumChannel (decoderKrausFamily_complete h)
noncomputable def idealLogicalTOutputState (m w : Nat) : LogicalRegister m w :=
  HH18PuncturedReedMuller.logicalT w m (logicalPlus m w)
theorem idealLogicalTOutputState_normSq (m w : Nat) :
    ‖idealLogicalTOutputState m w‖ ^ 2 = 1 := by
  have hnorm : ‖idealLogicalTOutputState m w‖ = 1 := by
    change ‖(HH18PuncturedReedMuller.logicalT w m).toLinearIsometryEquiv
      (logicalPlus m w)‖ = 1
    rw [(HH18PuncturedReedMuller.logicalT w m).toLinearIsometryEquiv.norm_map]
    exact logicalPlus_norm m w
  rw [hnorm]
  norm_num
noncomputable def idealLogicalTOutput (m w : Nat) :
    DensityOperator (LogicalRegister m w) :=
  DensityOperator.pureDensity (idealLogicalTOutputState m w)
    (idealLogicalTOutputState_normSq m w)
noncomputable def outputTraceError {m w : Nat}
    (rho sigma : DensityOperator (LogicalRegister m w)) : Real :=
  traceNorm (rho.toOperator - sigma.toOperator)
end HH18Parameterized
end Distillation
end QEC


