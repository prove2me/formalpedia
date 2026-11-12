-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
-- name    : QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:25:24.264254+00:00
-- url     : https://prove2.me/theorems/88cbd0db-88ee-4c68-97b9-0602eb583592
-- title:
--   Punctured Reed Muller
-- statement:
--   Definitions and structural lemmas for Punctured Reed Muller, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/PuncturedReedMuller.lean

import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LinearCode_symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_exists_systematicKeptLift_add_shortened
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dualContainment
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_shortenedReedMullerCode_dual_eq_punctured
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicCoset_weight_add_logical_dvd
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicKeptLift_mem_puncturedReedMullerCode
import Theorems.Thm_QEC_Coding_PuncturedReedMuller_systematicKeptLift_mem_shortenedReedMullerCode_iff
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseAmplitude_two_pi_mul_int
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_allSitePhase_apply
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
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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
namespace HH18PuncturedReedMuller
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
abbrev PhysicalSite (m w : Nat) := KeptPoint m w
abbrev LogicalSite (m w : Nat) := LowPoint m w
abbrev CodeBasisIndex {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :=
  Fin (Dimension C)
noncomputable def codeBasis {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    Module.Basis (CodeBasisIndex C) (ZMod 2) C.carrier :=
  Module.finBasis (ZMod 2) C.carrier
def codeBasisWord {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) (i : CodeBasisIndex C) :
    Word (ZMod 2) ι :=
  codeBasis C i
noncomputable def codeParityCheck {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) (CodeBasisIndex C) where
  toFun word i := wordPairing (codeBasisWord C i) word
  map_add' := by
    intro left right
    funext i
    exact (wordPairing (F := ZMod 2) (codeBasisWord C i)).map_add left right
  map_smul' := by
    intro scalar word
    funext i
    exact (wordPairing (F := ZMod 2) (codeBasisWord C i)).map_smul scalar word
theorem codeParityCheck_row {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) (i : CodeBasisIndex C) :
    parityCheckRow (codeParityCheck C) i = codeBasisWord C i := by
  classical
  ext j
  simp [parityCheckRow, wordLinearMapTranspose, codeParityCheck,
    codeBasisWord, wordPairing_apply, dotProduct]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro other hne
      simp [hne]
  · intro other hne
    simp [hne]
theorem codeParityCheck_rowCode {ι : Type} [Fintype ι]
    (C : LinearCode (ZMod 2) ι) :
    parityCheckRowCode (codeParityCheck C) = C := by
  have hcarrier :
      (parityCheckRowCode (codeParityCheck C)).carrier = C.carrier := by
    ext word
    constructor
    · rintro ⟨coefficients, rfl⟩
      rw [wordLinearMapTranspose_eq_sum_parityCheckRows]
      simp_rw [codeParityCheck_row]
      exact Submodule.sum_mem C.carrier fun i _ =>
        C.carrier.smul_mem _ (codeBasis C i).property
    · intro hword
      let wordInCode : C.carrier := ⟨word, hword⟩
      refine ⟨fun i => (codeBasis C).repr wordInCode i, ?_⟩
      rw [wordLinearMapTranspose_eq_sum_parityCheckRows]
      simp_rw [codeParityCheck_row]
      change
        (∑ x, (codeBasis C).repr wordInCode x •
          ((codeBasis C x : C.carrier) : Word (ZMod 2) ι)) = word
      simpa only [Submodule.coe_sum, Submodule.coe_smul, wordInCode] using
        congrArg Subtype.val ((codeBasis C).sum_repr wordInCode)
  cases hleft : parityCheckRowCode (codeParityCheck C) with
  | mk leftCarrier =>
      cases hright : C with
      | mk rightCarrier =>
          rw [hleft, hright] at hcarrier
          change leftCarrier = rightCarrier at hcarrier
          cases hcarrier
          rfl
abbrev XCheckIndex (w r m : Nat) :=
  CodeBasisIndex (shortenedReedMullerCode r m w)
abbrev ZCheckIndex (w r m : Nat) :=
  CodeBasisIndex (shortenedReedMullerCode (m - r - 1) m w)
noncomputable def xCheckBasis (w r m : Nat) :
    Module.Basis (XCheckIndex w r m) (ZMod 2)
      (shortenedReedMullerCode r m w).carrier :=
  codeBasis (shortenedReedMullerCode r m w)
noncomputable def zCheckBasis (w r m : Nat) :
    Module.Basis (ZCheckIndex w r m) (ZMod 2)
      (shortenedReedMullerCode (m - r - 1) m w).carrier :=
  codeBasis (shortenedReedMullerCode (m - r - 1) m w)
def xCheckWord (w r m : Nat) (i : XCheckIndex w r m) :
    Word (ZMod 2) (PhysicalSite m w) :=
  xCheckBasis w r m i
def zCheckWord (w r m : Nat) (i : ZCheckIndex w r m) :
    Word (ZMod 2) (PhysicalSite m w) :=
  zCheckBasis w r m i
noncomputable def xParityCheck (w r m : Nat) :
    Word (ZMod 2) (PhysicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (XCheckIndex w r m) :=
  codeParityCheck (shortenedReedMullerCode r m w)
noncomputable def zParityCheck (w r m : Nat) :
    Word (ZMod 2) (PhysicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (ZCheckIndex w r m) :=
  codeParityCheck (shortenedReedMullerCode (m - r - 1) m w)
@[simp]
theorem parityCheckRow_xParityCheck (w r m : Nat) (i : XCheckIndex w r m) :
    parityCheckRow (xParityCheck w r m) i = xCheckWord w r m i :=
  codeParityCheck_row (shortenedReedMullerCode r m w) i
@[simp]
theorem parityCheckRow_zParityCheck (w r m : Nat) (i : ZCheckIndex w r m) :
    parityCheckRow (zParityCheck w r m) i = zCheckWord w r m i :=
  codeParityCheck_row (shortenedReedMullerCode (m - r - 1) m w) i
theorem xParityCheck_rowCode (w r m : Nat) :
    parityCheckRowCode (xParityCheck w r m) =
      shortenedReedMullerCode r m w :=
  codeParityCheck_rowCode (shortenedReedMullerCode r m w)
theorem zParityCheck_rowCode (w r m : Nat) :
    parityCheckRowCode (zParityCheck w r m) =
      shortenedReedMullerCode (m - r - 1) m w :=
  codeParityCheck_rowCode (shortenedReedMullerCode (m - r - 1) m w)
noncomputable def xCode (w r m : Nat) :
    LinearCode (ZMod 2) (PhysicalSite m w) :=
  parityCheckRowCode (xParityCheck w r m)
noncomputable def zCode (w r m : Nat) :
    LinearCode (ZMod 2) (PhysicalSite m w) :=
  parityCheckRowCode (zParityCheck w r m)
@[simp]
theorem xCode_eq_shortened (w r m : Nat) :
    xCode w r m = shortenedReedMullerCode r m w :=
  xParityCheck_rowCode w r m
@[simp]
theorem zCode_eq_shortened (w r m : Nat) :
    zCode w r m = shortenedReedMullerCode (m - r - 1) m w :=
  zParityCheck_rowCode w r m
theorem cssDualContainment {w r m : Nat} (h : Admissible w r m) :
    (zCode w r m).carrier ≤ (xCode w r m).dual.carrier := by
  rw [xCode_eq_shortened, zCode_eq_shortened]
  exact shortenedReedMullerCode_dualContainment h
theorem parityCheckRows_orthogonal {w r m : Nat} (h : Admissible w r m) :
    ∀ z x,
      wordPairing
        (parityCheckRow (zParityCheck w r m) z)
        (parityCheckRow (xParityCheck w r m) x) = 0 :=
  (parityCheckRows_orthogonal_iff_rowCode_le_dual
    (zParityCheck w r m) (xParityCheck w r m)).2 (cssDualContainment h)
noncomputable def checkGenerator (w r m : Nat) :
    Sum (ZCheckIndex w r m) (XCheckIndex w r m) →
      PauliSymplectic.Binary (PhysicalSite m w) :=
  binaryCSSParityCheckGenerators (zParityCheck w r m) (xParityCheck w r m)
theorem checkGenerator_commutes {w r m : Nat} (h : Admissible w r m) :
    ∀ left right,
      PauliSymplectic.Commutes
        (checkGenerator w r m left) (checkGenerator w r m right) := by
  intro left right
  exact
    (binaryCSSStabilizerCodeOfParityChecks
      (zParityCheck w r m) (xParityCheck w r m)
      (parityCheckRows_orthogonal h)).isotropic
      (checkGenerator w r m left)
      (binaryCSSParityCheckGenerator_mem_checkSet
        (zParityCheck w r m) (xParityCheck w r m) left)
      (checkGenerator w r m right)
      (binaryCSSParityCheckGenerator_mem_checkSet
        (zParityCheck w r m) (xParityCheck w r m) right)
noncomputable def stabilizer {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode (ZMod 2) (PhysicalSite m w)
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  binaryCSSStabilizerCodeOfParityChecks
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)
noncomputable def sourceValidStabilizer {w r m : Nat}
    (h : Admissible w r m) :
    StabilizerCode.SourceValidBinary (PhysicalSite m w) :=
  binaryCSSSourceValidStabilizerOfParityChecks
    (zParityCheck w r m) (xParityCheck w r m)
    (parityCheckRows_orthogonal h)
noncomputable def cssCode {w r m : Nat} (h : Admissible w r m) :
    CSSCode (ZMod 2) (PhysicalSite m w)
      (Qubit.QubitRegister (PhysicalSite m w)) where
  xCode := xCode w r m
  zCode := zCode w r m
  stabilizer := stabilizer h
  orthogonal := by
    intro x hx z hz
    exact (xCode w r m).symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
      hx (cssDualContainment h hz)
@[simp]
theorem cssCode_xCode {w r m : Nat} (h : Admissible w r m) :
    (cssCode h).xCode = shortenedReedMullerCode r m w :=
  xCode_eq_shortened w r m
@[simp]
theorem cssCode_zCode {w r m : Nat} (h : Admissible w r m) :
    (cssCode h).zCode = shortenedReedMullerCode (m - r - 1) m w :=
  zCode_eq_shortened w r m
def allPositiveSyndrome (w r m : Nat) :
    JointSyndrome (Sum (ZCheckIndex w r m) (XCheckIndex w r m)) :=
  fun _ => StabilizerOutcome.positive
noncomputable def jointProjector {w r m : Nat} (h : Admissible w r m) :
    Operator (Qubit.QubitRegister (PhysicalSite m w)) :=
  jointStabilizerProjector (checkGenerator w r m)
    (checkGenerator_commutes h) (allPositiveSyndrome w r m)
noncomputable def keptSystematicLift {w r m : Nat} (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      Word (ZMod 2) (PhysicalSite m w) :=
  PuncturedReedMuller.systematicKeptLift h
theorem keptSystematicLift_mem_punctured {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    keptSystematicLift h logical ∈
      (puncturedReedMullerCode r m w).carrier :=
  systematicKeptLift_mem_puncturedReedMullerCode h logical
noncomputable abbrev LogicalQuotient (w r m : Nat) :=
  binaryCSSLogicalBasisQuotient (xCode w r m) (zCode w r m)
def keptSystematicLiftInZDual {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      (zCode w r m).dual.carrier :=
  (keptSystematicLift h).codRestrict (zCode w r m).dual.carrier fun logical => by
    rw [zCode_eq_shortened, shortenedReedMullerCode_dual_eq_punctured h]
    exact keptSystematicLift_mem_punctured h logical
noncomputable def logicalWordToQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) →ₗ[ZMod 2]
      LogicalQuotient w r m :=
  (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m)).mkQ.comp
    (keptSystematicLiftInZDual h)
@[simp]
theorem logicalWordToQuotient_apply {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    logicalWordToQuotient h logical =
      Submodule.Quotient.mk (keptSystematicLiftInZDual h logical) :=
  rfl
theorem keptSystematicLift_mem_xCode_iff {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    keptSystematicLift h logical ∈ (xCode w r m).carrier ↔ logical = 0 := by
  rw [xCode_eq_shortened]
  exact systematicKeptLift_mem_shortenedReedMullerCode_iff h logical
theorem logicalWordToQuotient_injective {w r m : Nat}
    (h : Admissible w r m) :
    Function.Injective (logicalWordToQuotient h) := by
  rw [injective_iff_map_eq_zero]
  intro logical hlogical
  have hmem :
      keptSystematicLift h logical ∈ (xCode w r m).carrier := by
    exact
      (Submodule.Quotient.mk_eq_zero
        (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).mp hlogical
  exact (keptSystematicLift_mem_xCode_iff h logical).1 hmem
theorem logicalWordToQuotient_surjective {w r m : Nat}
    (h : Admissible w r m) :
    Function.Surjective (logicalWordToQuotient h) := by
  intro quotient
  refine Submodule.Quotient.induction_on
    (p := binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))
    quotient ?_
  intro word
  have hpunctured :
      (word : Word (ZMod 2) (PhysicalSite m w)) ∈
        (puncturedReedMullerCode r m w).carrier := by
    have hshortened :
        (word : Word (ZMod 2) (PhysicalSite m w)) ∈
          (shortenedReedMullerCode (m - r - 1) m w).dual.carrier := by
      rw [← zCode_eq_shortened]
      exact word.2
    rw [shortenedReedMullerCode_dual_eq_punctured h] at hshortened
    exact hshortened
  obtain ⟨logical, shortened, hshortened, hdecompose⟩ :=
    exists_systematicKeptLift_add_shortened h hpunctured
  refine ⟨logical, ?_⟩
  apply (Submodule.Quotient.eq
    (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).2
  change
    keptSystematicLift h logical -
        (word : Word (ZMod 2) (PhysicalSite m w)) ∈
      (xCode w r m).carrier
  rw [xCode_eq_shortened]
  have hneg :
      -shortened ∈ (shortenedReedMullerCode r m w).carrier :=
    (shortenedReedMullerCode r m w).carrier.neg_mem hshortened
  convert hneg using 1
  change systematicKeptLift h logical -
      (word : Word (ZMod 2) (PhysicalSite m w)) = -shortened
  rw [← hdecompose]
  module
noncomputable def logicalWordEquivQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Word (ZMod 2) (LogicalSite m w) ≃ₗ[ZMod 2]
      LogicalQuotient w r m :=
  LinearEquiv.ofBijective (logicalWordToQuotient h)
    ⟨logicalWordToQuotient_injective h, logicalWordToQuotient_surjective h⟩
@[simp]
theorem logicalWordEquivQuotient_apply {w r m : Nat}
    (h : Admissible w r m)
    (logical : Word (ZMod 2) (LogicalSite m w)) :
    logicalWordEquivQuotient h logical = logicalWordToQuotient h logical :=
  rfl
noncomputable def logicalBasisEquivQuotient {w r m : Nat}
    (h : Admissible w r m) :
    Qubit.Bitstring (LogicalSite m w) ≃ LogicalQuotient w r m :=
  (bitstringWordEquiv (LogicalSite m w)).trans
    (logicalWordEquivQuotient h).toEquiv
noncomputable def logicalBasisReindex {w r m : Nat}
    (h : Admissible w r m) :
    Qubit.QubitRegister (LogicalSite m w) ≃ₗᵢ[Complex]
      EuclideanSpace Complex (LogicalQuotient w r m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Complex Complex
    (logicalBasisEquivQuotient h)
theorem quotientToCarrier_inner {w r m : Nat}
    (h : Admissible w r m)
    (phi chi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    inner Complex
        (binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
        (binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) chi) =
      (Nat.card (xCode w r m).carrier : Complex) *
        inner Complex phi chi := by
  exact Triorthogonal.binaryCSSLogicalBasisQuotientToCarrier_inner
    (xCode w r m) (zCode w r m) (cssDualContainment h) phi chi
noncomputable def cssNormalizationScalar {w r m : Nat}
    (_h : Admissible w r m) : Complex :=
  (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex)⁻¹
theorem cssNormalizationScalar_identity {w r m : Nat}
    (h : Admissible w r m) :
    starRingEnd Complex (cssNormalizationScalar h) *
        cssNormalizationScalar h *
        (Nat.card (xCode w r m).carrier : Complex) = 1 := by
  have hcard : 0 < Nat.card (xCode w r m).carrier := Nat.card_pos
  have hsqrtPos :
      0 < Real.sqrt (Nat.card (xCode w r m).carrier : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hsqrtNe :
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrtPos.ne'
  have hsquare :
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) *
          (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) =
        (Nat.card (xCode w r m).carrier : Complex) := by
    exact_mod_cast Real.mul_self_sqrt
      (by positivity : (0 : Real) ≤ Nat.card (xCode w r m).carrier)
  simp only [cssNormalizationScalar, map_inv₀]
  rw [show starRingEnd Complex
      (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) =
        (Real.sqrt (Nat.card (xCode w r m).carrier : Real) : Complex) by simp]
  rw [← hsquare]
  field_simp [hsqrtNe]
noncomputable def normalizedQuotientToCarrierLinearMap {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) →ₗ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  cssNormalizationScalar h •
    binaryCSSLogicalBasisQuotientToCarrier
      (xCode w r m) (zCode w r m) (cssDualContainment h)
@[simp]
theorem normalizedQuotientToCarrierLinearMap_apply {w r m : Nat}
    (h : Admissible w r m)
    (phi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    normalizedQuotientToCarrierLinearMap h phi =
      cssNormalizationScalar h •
        binaryCSSLogicalBasisQuotientToCarrier
          (xCode w r m) (zCode w r m) (cssDualContainment h) phi :=
  rfl
theorem normalizedQuotientToCarrierLinearMap_inner {w r m : Nat}
    (h : Admissible w r m)
    (phi chi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    inner Complex (normalizedQuotientToCarrierLinearMap h phi)
        (normalizedQuotientToCarrierLinearMap h chi) =
      inner Complex phi chi := by
  rw [normalizedQuotientToCarrierLinearMap_apply,
    normalizedQuotientToCarrierLinearMap_apply]
  calc
    inner Complex
          (cssNormalizationScalar h •
            binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
          (cssNormalizationScalar h •
            binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) chi) =
        starRingEnd Complex (cssNormalizationScalar h) *
          inner Complex
            (binaryCSSLogicalBasisQuotientToCarrier
              (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
            (cssNormalizationScalar h •
              binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) chi) :=
      inner_smul_left _ _ _
    _ = starRingEnd Complex (cssNormalizationScalar h) *
          (cssNormalizationScalar h *
            inner Complex
              (binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) phi)
              (binaryCSSLogicalBasisQuotientToCarrier
                (xCode w r m) (zCode w r m) (cssDualContainment h) chi)) := by
      rw [inner_smul_right]
    _ = starRingEnd Complex (cssNormalizationScalar h) *
          (cssNormalizationScalar h *
            ((Nat.card (xCode w r m).carrier : Complex) *
              inner Complex phi chi)) := by
      rw [quotientToCarrier_inner h]
    _ = (starRingEnd Complex (cssNormalizationScalar h) *
          cssNormalizationScalar h *
          (Nat.card (xCode w r m).carrier : Complex)) *
        inner Complex phi chi := by ring
    _ = inner Complex phi chi := by
      rw [cssNormalizationScalar_identity h, one_mul]
noncomputable def normalizedQuotientToCarrierLinearIsometry {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) →ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  (normalizedQuotientToCarrierLinearMap h).isometryOfInner
    (normalizedQuotientToCarrierLinearMap_inner h)
noncomputable def normalizedQuotientToCarrier {w r m : Nat}
    (h : Admissible w r m) :
    EuclideanSpace Complex (LogicalQuotient w r m) ≃ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier := by
  let reconstruction := normalizedQuotientToCarrierLinearIsometry h
  have hdim :
      Module.finrank Complex (EuclideanSpace Complex (LogicalQuotient w r m)) =
        Module.finrank Complex (cssCode h).stabilizer.code.carrier := by
    have hraw :=
      (binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
        (xCode w r m) (zCode w r m) (cssDualContainment h)).finrank_eq.symm
    rw [finrank_euclideanSpace] at hraw
    rw [finrank_euclideanSpace]
    exact hraw
  have hsurjective : Function.Surjective reconstruction :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      reconstruction.injective
  exact LinearIsometryEquiv.ofSurjective reconstruction hsurjective
@[simp]
theorem normalizedQuotientToCarrier_apply {w r m : Nat}
    (h : Admissible w r m)
    (phi : EuclideanSpace Complex (LogicalQuotient w r m)) :
    normalizedQuotientToCarrier h phi =
      normalizedQuotientToCarrierLinearMap h phi :=
  rfl
noncomputable def encoding {w r m : Nat} (h : Admissible w r m) :
    Qubit.QubitRegister (LogicalSite m w) ≃ₗᵢ[Complex]
      (cssCode h).stabilizer.code.carrier :=
  (logicalBasisReindex h).trans (normalizedQuotientToCarrier h)
theorem encoding_apply_of_mem {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (LogicalSite m w))
    {bits : Qubit.Bitstring (PhysicalSite m w)}
    (hbits :
      bitstringWordEquiv (PhysicalSite m w) bits ∈
        (zCode w r m).dual.carrier) :
    (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits =
      cssNormalizationScalar h *
        psi ((logicalBasisEquivQuotient h).symm
          (Submodule.Quotient.mk
            ⟨bitstringWordEquiv (PhysicalSite m w) bits, hbits⟩)) := by
  change cssNormalizationScalar h *
      binaryCSSLogicalBasisQuotientToQubitRegister
        (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) bits = _
  rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) hbits]
  rfl
theorem encoding_apply_of_not_mem {w r m : Nat}
    (h : Admissible w r m)
    (psi : Qubit.QubitRegister (LogicalSite m w))
    {bits : Qubit.Bitstring (PhysicalSite m w)}
    (hbits :
      bitstringWordEquiv (PhysicalSite m w) bits ∉
        (zCode w r m).dual.carrier) :
    (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits = 0 := by
  change cssNormalizationScalar h *
      binaryCSSLogicalBasisQuotientToQubitRegister
        (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) bits = 0
  rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    (xCode w r m) (zCode w r m) (logicalBasisReindex h psi) hbits]
  simp
noncomputable def logicalBasisWord {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    Word (ZMod 2) (PhysicalSite m w) :=
  keptSystematicLift h (canonicalBasisWord logical)
noncomputable def logicalXPauli {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    PauliSymplectic.Binary (PhysicalSite m w) :=
  cssXCheck (logicalBasisWord h logical)
noncomputable def logicalZPauli {w r m : Nat}
    (h : Admissible w r m) (logical : LogicalSite m w) :
    PauliSymplectic.Binary (PhysicalSite m w) :=
  cssZCheck (logicalBasisWord h logical)
noncomputable def encodedCode {w r m : Nat} (h : Admissible w r m) :
    EncodedCode (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) where
  code := (cssCode h).stabilizer.code
  encoding := encoding h
@[simp]
theorem encodedCode_code {w r m : Nat} (h : Admissible w r m) :
    (encodedCode h).code = (cssCode h).stabilizer.code :=
  rfl
@[simp]
theorem encodedCode_encoding {w r m : Nat} (h : Admissible w r m) :
    (encodedCode h).encoding = encoding h :=
  rfl
def phaseAngle (nu : Nat) : Real :=
  (2 * Real.pi) / ((2 ^ nu : Nat) : Real)
theorem phaseAmplitude_eq_neg_of_weight_add_dvd {w m nu : Nat}
    (physical : Word (ZMod 2) (PhysicalSite m w))
    (logical : Word (ZMod 2) (LogicalSite m w))
    (hdiv : 2 ^ nu ∣ HammingWeight physical + HammingWeight logical) :
    OneQubitMagic.phaseAmplitude
        (phaseAngle nu * (HammingWeight physical : Real)) =
      OneQubitMagic.phaseAmplitude
        (-phaseAngle nu * (HammingWeight logical : Real)) := by
  rcases hdiv with ⟨k, hk⟩
  have hangle :
      phaseAngle nu * (HammingWeight physical : Real) =
        -phaseAngle nu * (HammingWeight logical : Real) +
          (2 * Real.pi) * (k : Real) := by
    calc
      phaseAngle nu * (HammingWeight physical : Real) =
          phaseAngle nu *
              ((HammingWeight physical + HammingWeight logical : Nat) : Real) -
            phaseAngle nu * (HammingWeight logical : Real) := by
              push_cast
              ring
      _ = phaseAngle nu * ((2 ^ nu * k : Nat) : Real) -
            phaseAngle nu * (HammingWeight logical : Real) := by rw [hk]
      _ = -phaseAngle nu * (HammingWeight logical : Real) +
            (2 * Real.pi) * (k : Real) := by
              unfold phaseAngle
              push_cast
              have hdenominator : ((2 ^ nu : Nat) : Real) ≠ 0 := by positivity
              field_simp [hdenominator]
              ring
  have hperiod :
      OneQubitMagic.phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
    simpa using OneQubitMagic.phaseAmplitude_two_pi_mul_int (k : Int)
  rw [hangle, OneQubitMagic.phaseAmplitude_add, hperiod, mul_one]
theorem cosetWeightDivisible {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LogicalSite m w))
    (physical : (zCode w r m).dual.carrier)
    (hcoset : (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
      logicalWordToQuotient h logical) :
    2 ^ nu ∣ HammingWeight (physical : Word (ZMod 2) (PhysicalSite m w)) +
      HammingWeight logical := by
  rw [logicalWordToQuotient_apply] at hcoset
  have hresidual := (Submodule.Quotient.eq
    (binaryCSSXCodeInZDual (xCode w r m) (zCode w r m))).mp hcoset
  change (physical : Word (ZMod 2) (PhysicalSite m w)) -
      keptSystematicLift h logical ∈ (xCode w r m).carrier at hresidual
  rw [xCode_eq_shortened] at hresidual
  exact systematicCoset_weight_add_logical_dvd h hdegree logical hresidual
theorem cosetPhase {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (logical : Word (ZMod 2) (LogicalSite m w))
    (physical : (zCode w r m).dual.carrier)
    (hcoset : (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
      logicalWordToQuotient h logical)
    (psi : Qubit.QubitRegister (PhysicalSite m w))
    (bits : Qubit.Bitstring (PhysicalSite m w))
    (hbits : bitstringWordEquiv (PhysicalSite m w) bits = physical) :
    Triorthogonal.allSitePhase (Index := PhysicalSite m w) (phaseAngle nu) psi bits =
      OneQubitMagic.phaseAmplitude
        (-phaseAngle nu * (HammingWeight logical : Real)) * psi bits := by
  rw [Triorthogonal.allSitePhase_apply]
  have hphase := phaseAmplitude_eq_neg_of_weight_add_dvd
    (physical := (physical : Word (ZMod 2) (PhysicalSite m w)))
    (logical := logical)
    (cosetWeightDivisible h hdegree logical physical hcoset)
  rw [hbits]
  rw [hphase]
noncomputable def physicalAllSitePhase (w m nu : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  Triorthogonal.allSitePhase (Index := PhysicalSite m w) (phaseAngle nu)
noncomputable def logicalAllSitePhase (w m nu : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  Triorthogonal.allSitePhase (Index := LogicalSite m w) (-phaseAngle nu)
theorem phaseIntertwinesEncoding {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m)
    (psi : Qubit.QubitRegister (LogicalSite m w)) :
    physicalAllSitePhase w m nu
        (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) =
      (encoding h (logicalAllSitePhase w m nu psi) :
        Qubit.QubitRegister (PhysicalSite m w)) := by
  ext bits
  by_cases hbits : bitstringWordEquiv (PhysicalSite m w) bits ∈
      (zCode w r m).dual.carrier
  · let physical : (zCode w r m).dual.carrier :=
      ⟨bitstringWordEquiv (PhysicalSite m w) bits, hbits⟩
    let logicalBits : Qubit.Bitstring (LogicalSite m w) :=
      (logicalBasisEquivQuotient h).symm (Submodule.Quotient.mk physical)
    let logical : Word (ZMod 2) (LogicalSite m w) :=
      bitstringWordEquiv (LogicalSite m w) logicalBits
    have hcoset :
        (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
          logicalWordToQuotient h logical := by
      rw [← logicalWordEquivQuotient_apply h logical]
      change (Submodule.Quotient.mk physical : LogicalQuotient w r m) =
        logicalBasisEquivQuotient h logicalBits
      exact ((logicalBasisEquivQuotient h).apply_symm_apply
        (Submodule.Quotient.mk physical)).symm
    have hphysical : bitstringWordEquiv (PhysicalSite m w) bits = physical :=
      rfl
    calc
      physicalAllSitePhase w m nu
          (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits =
          OneQubitMagic.phaseAmplitude
              (-phaseAngle nu * (HammingWeight logical : Real)) *
            (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits := by
              exact cosetPhase h hdegree logical physical hcoset
                (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) bits hphysical
      _ = OneQubitMagic.phaseAmplitude
              (-phaseAngle nu * (HammingWeight logical : Real)) *
            (cssNormalizationScalar h * psi logicalBits) := by
              rw [encoding_apply_of_mem h psi hbits]
      _ = cssNormalizationScalar h *
            (logicalAllSitePhase w m nu psi) logicalBits := by
              rw [logicalAllSitePhase, Triorthogonal.allSitePhase_apply]
              change OneQubitMagic.phaseAmplitude
                  (-phaseAngle nu * (HammingWeight logical : Real)) *
                    (cssNormalizationScalar h * psi logicalBits) =
                cssNormalizationScalar h *
                  (OneQubitMagic.phaseAmplitude
                    (-phaseAngle nu * (HammingWeight logical : Real)) *
                    psi logicalBits)
              ring
      _ = (encoding h (logicalAllSitePhase w m nu psi) :
            Qubit.QubitRegister (PhysicalSite m w)) bits := by
              rw [encoding_apply_of_mem h
                (logicalAllSitePhase w m nu psi) hbits]
  · rw [physicalAllSitePhase, Triorthogonal.allSitePhase_apply,
      encoding_apply_of_not_mem h psi hbits,
      encoding_apply_of_not_mem h (logicalAllSitePhase w m nu psi) hbits]
    simp
theorem physicalAllSitePhase_implements_logicalAllSitePhase {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m) :
    (encodedCode h).ImplementsLogicalGate
      (physicalAllSitePhase w m nu) (logicalAllSitePhase w m nu) := by
  intro psi
  change physicalAllSitePhase w m nu
      (encoding h psi : Qubit.QubitRegister (PhysicalSite m w)) =
    (encoding h (logicalAllSitePhase w m nu psi) :
      Qubit.QubitRegister (PhysicalSite m w))
  exact phaseIntertwinesEncoding h hdegree psi
noncomputable def sitewisePhaseTransversalLogicalGate {w r m nu : Nat}
    (h : Admissible w r m) (hdegree : nu * r < m) :
    SitewiseTransversalLogicalGate (encodedCode h)
      (logicalAllSitePhase w m nu)
      (Triorthogonal.diagonalPhaseGateModel (Index := PhysicalSite m w)) where
  physicalGate := physicalAllSitePhase w m nu
  implements := physicalAllSitePhase_implements_logicalAllSitePhase h hdegree
  transversality := by
    simpa only [physicalAllSitePhase] using
      (Triorthogonal.allSitePhaseTransversality
        (Index := PhysicalSite m w) (phaseAngle nu))
noncomputable def physicalT (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  physicalAllSitePhase w m 3
noncomputable def logicalTInv (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  logicalAllSitePhase w m 3
noncomputable def physicalT_sitewise_transversal {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    SitewiseTransversalLogicalGate (encodedCode h) (logicalTInv w m)
      (Triorthogonal.diagonalPhaseGateModel (Index := PhysicalSite m w)) := by
  simpa only [physicalT, logicalTInv] using
    (sitewisePhaseTransversalLogicalGate (nu := 3) h hdegree)
noncomputable def physicalTInv (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (PhysicalSite m w))
      (Qubit.QubitRegister (PhysicalSite m w)) :=
  (physicalT w m).symm
noncomputable def logicalT (w m : Nat) :
    UnitaryTransport (Qubit.QubitRegister (LogicalSite m w))
      (Qubit.QubitRegister (LogicalSite m w)) :=
  (logicalTInv w m).symm
end HH18PuncturedReedMuller
end Distillation
end QEC


