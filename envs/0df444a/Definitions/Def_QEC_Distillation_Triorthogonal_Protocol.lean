-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
-- name    : QEC_Distillation_Triorthogonal_Protocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:50:12.447083+00:00
-- url     : https://prove2.me/theorems/ed1e9941-8e50-4f79-b1e5-0f8fa3a200bc
-- title:
--   Protocol
-- statement:
--   Definitions and structural lemmas for Protocol, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenCode_weightSum
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_diagonalAResource_weight
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_weight_nonneg
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_weight_sum
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_independentNoisyTChannel_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_intertwines_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedMagicState_inner_self
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedPlusState_inner_self
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_inner_self
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_allSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_smul_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_flipSupport_singleton
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
attribute [local simp] QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
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
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace Triorthogonal
namespace BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
abbrev LogicalRegister (q : Nat) := Qubit.QubitRegister (OddRow q)
abbrev PhysicalRegister (q : Nat) := Qubit.QubitRegister (Column q)
abbrev PhysicalError (q : Nat) := Word (ZMod 2) (Column q)
abbrev Syndrome := JointSyndrome EvenRow
def xChecks (q : Nat) (check : EvenRow) : Binary (Column q) :=
  cssXCheck (evenWord check)
theorem xChecks_commute (q : Nat) (left right : EvenRow) :
    Commutes (xChecks q left) (xChecks q right) :=
  cssXCheck_commutes_cssXCheck _ _
def trivialSyndrome : Syndrome := fun _ => .positive
def syndromeOfError {q : Nat} (error : PhysicalError q) : Syndrome :=
  fun check =>
    if wordPairing (evenWord check) error = 0 then .positive else .negative
def Accepts {q : Nat} (error : PhysicalError q) : Prop :=
  syndromeOfError error = trivialSyndrome
instance {q : Nat} (error : PhysicalError q) : Decidable (Accepts error) :=
  inferInstanceAs (Decidable (syndromeOfError error = trivialSyndrome))
theorem accepts_iff_pairing_even_rows {q : Nat} (error : PhysicalError q) :
    Accepts error ↔ ∀ check, wordPairing (evenWord check) error = 0 := by
  constructor
  · intro h check
    have hs := congrFun h check
    simp only [syndromeOfError, trivialSyndrome] at hs
    split at hs
    · assumption
    · contradiction
  · intro h
    funext check
    simp [syndromeOfError, trivialSyndrome, h check]
theorem accepts_iff_mem_evenCode_dual {q : Nat} (error : PhysicalError q) :
    Accepts error ↔ error ∈ (family q).evenCode.dual.carrier := by
  rw [accepts_iff_pairing_even_rows, LinearCode.mem_dual]
  constructor
  · intro h word hword
    change word ∈ Submodule.span (ZMod 2) (Set.range (@evenWord q)) at hword
    induction hword using Submodule.span_induction with
    | mem word hword =>
        rcases hword with ⟨check, rfl⟩
        simpa [wordPairing_apply, dotProduct_comm] using h check
    | zero => simp
    | add left right _ _ hleft hright =>
        rw [(wordPairing error).map_add, hleft, hright, add_zero]
    | smul scalar word _ hword =>
        rw [(wordPairing error).map_smul, hword, smul_zero]
  · intro h check
    have := h (evenWord check) ((family q).evenRow_mem_evenCode check)
    simpa [wordPairing_apply, dotProduct_comm] using this
def syndromeOutcome (syndrome : Syndrome) : DistillationOutcome :=
  if syndrome = trivialSyndrome then .accepted else .rejected
@[simp] theorem syndromeOutcome_trivial :
    syndromeOutcome trivialSyndrome = .accepted := by
  simp [syndromeOutcome]
def fullSyndromeInstrument (q : Nat) :
    FiniteInstrument Syndrome Syndrome (PhysicalRegister q) (PhysicalRegister q) :=
  jointStabilizerInstrument (xChecks q) (xChecks_commute q)
def protocolSyndromeInstrument (q : Nat) :
    FiniteInstrument Syndrome DistillationOutcome
      (PhysicalRegister q) (PhysicalRegister q) where
  kraus := jointStabilizerKrausFamily (xChecks q) (xChecks_commute q)
  observe := syndromeOutcome
@[simp] theorem protocolSyndromeInstrument_kraus (q : Nat) :
    (protocolSyndromeInstrument q).kraus =
      jointStabilizerKrausFamily (xChecks q) (xChecks_commute q) :=
  rfl
theorem protocolSyndromeInstrument_complete (q : Nat) :
    (protocolSyndromeInstrument q).kraus.Complete :=
  jointStabilizerKrausFamily_complete (xChecks q) (xChecks_commute q)
def syndromeMeasurementChannel (q : Nat) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  (protocolSyndromeInstrument q).kraus.toQuantumChannel
    (protocolSyndromeInstrument_complete q)
def correctionChannel (q : Nat) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  QuantumChannel.unitaryConj (family q).physicalCliffordCorrection
def correctedNoisyTChannel (q : Nat) (p : ErrorParameter) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  QuantumChannel.comp (correctionChannel q)
    (independentNoisyTChannel (Index := Column q) p)
def physicalOperation (q : Nat) (p : ErrorParameter) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  QuantumChannel.comp (syndromeMeasurementChannel q)
    (correctedNoisyTChannel q p)
theorem encodedPlusAmbient_normSq (q : Nat) :
    ‖((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)‖ ^ 2 = 1 := by
  have hinner := (family q).encodedPlusState_inner_self (isTriorthogonal q)
  have hambient :
      inner Complex
          (((family q).encodedPlusState (isTriorthogonal q) :
            (family q).cssQuantumCode.carrier) : PhysicalRegister q)
          (((family q).encodedPlusState (isTriorthogonal q) :
            (family q).cssQuantumCode.carrier) : PhysicalRegister q) = 1 := by
    simpa using hinner
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hambient]
  norm_num
def encodedPlusInput (q : Nat) : DensityOperator (PhysicalRegister q) :=
  DensityOperator.pureDensity
    ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)
    (encodedPlusAmbient_normSq q)
def preSyndromeState (q : Nat) (p : ErrorParameter) :
    DensityOperator (PhysicalRegister q) :=
  (correctedNoisyTChannel q p).mapDensity (encodedPlusInput q)
def rawEndpoint (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) : Operator (PhysicalRegister q) :=
  (protocolSyndromeInstrument q).branchOperator outcome (preSyndromeState q p).toOperator
def endpointWeight (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) : ℝ :=
  (protocolSyndromeInstrument q).bornWeight outcome (preSyndromeState q p)
def endpointConditional (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) (hpos : 0 < endpointWeight q p outcome) :
    DensityOperator (PhysicalRegister q) :=
  (protocolSyndromeInstrument q).conditionalDensity outcome
    (preSyndromeState q p) hpos
@[simp] theorem endpointConditional_toOperator (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) (hpos : 0 < endpointWeight q p outcome) :
    (endpointConditional q p outcome hpos).toOperator =
      ((endpointWeight q p outcome : Complex)⁻¹) • rawEndpoint q p outcome :=
  rfl
theorem phaseAmplitude_nat_mul (theta : ℝ) (n : Nat) :
    OneQubitMagic.phaseAmplitude (n * theta) =
      OneQubitMagic.phaseAmplitude theta ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, OneQubitMagic.phaseAmplitude_add,
        ih, one_mul, pow_succ]
theorem allSiteT_logicalPlusState (q : Nat) :
    (allSiteT (Index := OddRow q))
        (BinaryRowFamily.logicalPlusState (OddRow q)) =
      BinaryRowFamily.logicalMagicState (OddRow q) := by
  ext bits
  rw [allSiteT_apply]
  simp only [BinaryRowFamily.logicalPlusState_apply,
    BinaryRowFamily.logicalMagicState_apply, BinaryRowFamily.piDivFourPhase]
  rw [show Real.pi / 4 *
      (HammingWeight (bitstringWordEquiv (OddRow q) bits) : Real) =
      (HammingWeight (bitstringWordEquiv (OddRow q) bits) : Nat) *
        (Real.pi / 4) by ring]
  rw [phaseAmplitude_nat_mul]
  ring
theorem correctedAllSiteT_encodedPlusState (q : Nat) :
    (family q).correctedAllSiteT
        ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q) =
      ((family q).encodedMagicState (isTriorthogonal q) : PhysicalRegister q) := by
  change (family q).correctedAllSiteT
      ((family q).encoding (isTriorthogonal q)
        (BinaryRowFamily.logicalPlusState (OddRow q)) : PhysicalRegister q) =
    ((family q).encoding (isTriorthogonal q)
      (BinaryRowFamily.logicalMagicState (OddRow q)) : PhysicalRegister q)
  rw [(family q).correctedAllSiteT_intertwines_encoding
    (isTriorthogonal q) (BinaryRowFamily.logicalPlusState (OddRow q))]
  rw [allSiteT_logicalPlusState]
def errorBranchState {q : Nat} (error : PhysicalError q) : PhysicalRegister q :=
  toQubitOperator (cssZCheck error)
    ((family q).encodedMagicState (isTriorthogonal q) : PhysicalRegister q)
theorem errorBranchState_normSq {q : Nat} (error : PhysicalError q) :
    ‖errorBranchState error‖ ^ 2 = 1 := by
  have hinner : inner Complex (errorBranchState error) (errorBranchState error) = 1 := by
    simp only [errorBranchState]
    rw [← LinearMap.adjoint_inner_left]
    have hunit := toQubitOperator_adjoint_comp_self (cssZCheck error)
    have happ :
        LinearMap.adjoint (toQubitOperator (cssZCheck error))
            (toQubitOperator (cssZCheck error)
              ((family q).encodedMagicState (isTriorthogonal q) : PhysicalRegister q)) =
          ((family q).encodedMagicState (isTriorthogonal q) : PhysicalRegister q) := by
      have := LinearMap.congr_fun hunit
        ((family q).encodedMagicState (isTriorthogonal q) : PhysicalRegister q)
      simpa [LinearMap.comp_apply] using this
    rw [happ]
    have hmagic := (family q).encodedMagicState_inner_self (isTriorthogonal q)
    simpa using hmagic
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
  norm_num
def errorBranchDensity {q : Nat} (error : PhysicalError q) :
    DensityOperator (PhysicalRegister q) :=
  DensityOperator.pureDensity (errorBranchState error)
    (errorBranchState_normSq error)
theorem sandwich_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]
theorem unitary_conj_rankOne {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (psi : H) :
    U.conjOperator
        (InnerProductSpace.rankOne Complex psi psi).toLinearMap =
      (InnerProductSpace.rankOne Complex (U psi) (U psi)).toLinearMap := by
  change U.toLinearEquiv.toLinearMap.comp
      ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
        U.toLinearEquiv.symm.toLinearMap) = _
  rw [← U.adjoint_toLinearMap]
  exact sandwich_rankOne U.toLinearEquiv.toLinearMap psi
theorem selfAdjoint_sandwich_rankOne {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (L : Operator H) (hL : LinearMap.adjoint L = L) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp L) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  have h := sandwich_rankOne L psi
  rw [hL] at h
  exact h
theorem correction_commutes_errorZ (q : Nat) (error : PhysicalError q)
    (psi : PhysicalRegister q) :
    (family q).physicalCliffordCorrection
        (toQubitOperator (cssZCheck error) psi) =
      toQubitOperator (cssZCheck error)
        ((family q).physicalCliffordCorrection psi) := by
  ext bits
  simp [BinaryRowFamily.physicalCliffordCorrection_apply,
    toQubitOperator_apply, cssZCheck, xSupport, zSupport]
  ring
theorem corrected_errorBranch_on_encodedPlus (q : Nat)
    (error : PhysicalError q) :
    (family q).physicalCliffordCorrection
        (registerBranchOperator error
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)) =
      errorBranchState error := by
  rw [registerBranchOperator]
  change (family q).physicalCliffordCorrection
      (toQubitOperator (cssZCheck error)
        ((allSiteT (Index := Column q))
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))) = _
  rw [correction_commutes_errorZ]
  change toQubitOperator (cssZCheck error)
      ((family q).correctedAllSiteT
        ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)) = _
  rw [correctedAllSiteT_encodedPlusState]
  rfl
set_option maxHeartbeats 800000 in
/-- The pre-syndrome density is the actual independent mixture of physical branches. -/
theorem preSyndromeState_toOperator (q : Nat) (p : ErrorParameter) :
    (preSyndromeState q p).toOperator =
      ∑ error : PhysicalError q,
        (errorWordProbability p error : Complex) •
          (errorBranchDensity error).toOperator := by
  change (correctionChannel q)
      ((independentNoisyTChannel (Index := Column q) p)
        (encodedPlusInput q).toOperator) = _
  rw [independentNoisyTChannel_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro error _
  rw [map_smul]
  congr 1
  rw [correctionChannel, QuantumChannel.unitaryConj_apply]
  rw [encodedPlusInput, DensityOperator.pureDensity_toOperator]
  rw [unitary_conj_rankOne]
  rw [show (toQubitOperator (cssZCheck error)).comp
      ((InnerProductSpace.rankOne Complex
        ((allSiteT (Index := Column q))
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))
        ((allSiteT (Index := Column q))
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))).toLinearMap.comp
        (toQubitOperator (cssZCheck error))) =
      (InnerProductSpace.rankOne Complex
        (registerBranchOperator error
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))
        (registerBranchOperator error
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))).toLinearMap by
    apply selfAdjoint_sandwich_rankOne
    rw [adjoint_toQubitOperator_eq_binaryDagger]
    simp]
  rw [show (family q).physicalCliffordCorrection.conjOperator
      (InnerProductSpace.rankOne Complex
        (registerBranchOperator error
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))
        (registerBranchOperator error
          ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q))).toLinearMap =
      (InnerProductSpace.rankOne Complex
        ((family q).physicalCliffordCorrection
          (registerBranchOperator error
            ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)))
        ((family q).physicalCliffordCorrection
          (registerBranchOperator error
            ((family q).encodedPlusState (isTriorthogonal q) : PhysicalRegister q)))).toLinearMap by
    exact unitary_conj_rankOne (family q).physicalCliffordCorrection _]
  rw [corrected_errorBranch_on_encodedPlus]
  rfl
noncomputable def protocolBranchLinearMap (q : Nat)
    (outcome : DistillationOutcome) :
    Operator (PhysicalRegister q) →ₗ[Complex] Operator (PhysicalRegister q) where
  toFun := (protocolSyndromeInstrument q).branchOperator outcome
  map_add' := by
    intro A B
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro syndrome _
    by_cases hobserve :
        (protocolSyndromeInstrument q).observe syndrome = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply, map_add]
    · simp [hobserve]
  map_smul' := by
    intro scalar A
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro syndrome _
    by_cases hobserve :
        (protocolSyndromeInstrument q).observe syndrome = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]
def rawSuccessMass (q : Nat) (p : ErrorParameter) : ℝ :=
  ∑ error : PhysicalError q,
    if Accepts error then errorWordProbability p error else 0
def realBinarySign (bit : ZMod 2) : ℝ :=
  if bit = 0 then 1 else -1
theorem realBinarySign_add (left right : ZMod 2) :
    realBinarySign (left + right) =
      realBinarySign left * realBinarySign right := by
  by_cases hleft : left = 0
  · subst left
    simp [realBinarySign]
  · have hleftOne := zmod_two_eq_one_of_ne_zero hleft
    subst left
    by_cases hright : right = 0
    · subst right
      simp [realBinarySign]
    · have hrightOne := zmod_two_eq_one_of_ne_zero hright
      subst right
      have hone_add_one : (1 : ZMod 2) + 1 = 0 := by decide
      have hone_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
      simp [realBinarySign, hone_add_one, hone_ne_zero]
noncomputable instance evenCodeDualMembershipDecidable (q : Nat) :
    DecidablePred (fun error : PhysicalError q =>
      error ∈ (family q).evenCode.dual.carrier) :=
  Classical.decPred _
theorem realBinarySign_add_of_ne_zero (left right : ZMod 2)
    (hright : right ≠ 0) :
    realBinarySign (left + right) = -realBinarySign left := by
  rw [realBinarySign_add]
  have hsign : realBinarySign right = -1 := by
    simp [realBinarySign, hright]
  rw [hsign]
  ring
def evenCodeTranslate {q : Nat}
    (word : (family q).evenCode.carrier) :
    (family q).evenCode.carrier ≃ (family q).evenCode.carrier where
  toFun := fun codeword => codeword + word
  invFun := fun codeword => codeword - word
  left_inv := by
    intro codeword
    exact add_sub_cancel_right codeword word
  right_inv := by
    intro codeword
    exact sub_add_cancel codeword word
@[simp] theorem coe_evenCodeTranslate_apply {q : Nat}
    (word codeword : (family q).evenCode.carrier) :
    ((evenCodeTranslate word codeword : (family q).evenCode.carrier) :
      PhysicalError q) = (codeword : PhysicalError q) + word :=
  rfl
def evenCodeBinaryCharacter {q : Nat}
    (codeword : (family q).evenCode.carrier) (error : PhysicalError q) : ℝ :=
  realBinarySign (wordPairing (codeword : PhysicalError q) error)
theorem evenCodeBinaryCharacter_translate {q : Nat}
    (word codeword : (family q).evenCode.carrier) (error : PhysicalError q)
    (hword : wordPairing (word : PhysicalError q) error ≠ 0) :
    evenCodeBinaryCharacter (evenCodeTranslate word codeword) error =
      -evenCodeBinaryCharacter codeword error := by
  unfold evenCodeBinaryCharacter
  change realBinarySign
      (wordPairing
        ((codeword : PhysicalError q) + (word : PhysicalError q)) error) = _
  rw [map_add]
  exact realBinarySign_add_of_ne_zero _ _ hword
theorem evenCode_binaryCharacter_sum (q : Nat) (error : PhysicalError q) :
    (∑ codeword : (family q).evenCode.carrier,
      evenCodeBinaryCharacter codeword error) =
      if error ∈ (family q).evenCode.dual.carrier then
        Fintype.card (family q).evenCode.carrier else 0 := by
  classical
  letI : Fintype (family q).evenCode.carrier := Fintype.ofFinite _
  by_cases hdual : error ∈ (family q).evenCode.dual.carrier
  · have horth (codeword : (family q).evenCode.carrier) :
        wordPairing (codeword : PhysicalError q) error = 0 :=
      LinearCode.dual_orthogonal (family q).evenCode codeword.property hdual
    rw [if_pos hdual]
    simp [evenCodeBinaryCharacter, realBinarySign, horth]
  · obtain ⟨word, hword, hpair⟩ :=
      exists_carrier_wordPairing_ne_zero_of_not_mem_dual (family q).evenCode hdual
    let carrierWord : (family q).evenCode.carrier := ⟨word, hword⟩
    have hpair' : wordPairing (carrierWord : PhysicalError q) error ≠ 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using hpair
    have htranslate :
        (∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter codeword error) =
        ∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter (evenCodeTranslate carrierWord codeword) error := by
      symm
      exact (evenCodeTranslate carrierWord).sum_comp
        (fun codeword => evenCodeBinaryCharacter codeword error)
    rw [if_neg hdual]
    have hneg :
        (∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter codeword error) =
        -(∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter codeword error) := by
      calc
        (∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter codeword error) =
            ∑ codeword : (family q).evenCode.carrier,
              evenCodeBinaryCharacter (evenCodeTranslate carrierWord codeword) error :=
          htranslate
        _ = ∑ codeword : (family q).evenCode.carrier,
              -evenCodeBinaryCharacter codeword error := by
          apply Finset.sum_congr rfl
          intro codeword _
          exact evenCodeBinaryCharacter_translate carrierWord codeword error hpair'
        _ = -(∑ codeword : (family q).evenCode.carrier,
              evenCodeBinaryCharacter codeword error) := by
          rw [Finset.sum_neg_distrib]
    simpa using (CharZero.eq_neg_self_iff.mp hneg)
theorem realBinarySign_sum_eq_prod {ι : Type*} [DecidableEq ι]
    (sites : Finset ι) (term : ι → ZMod 2) :
    realBinarySign (∑ site ∈ sites, term site) =
      ∏ site ∈ sites, realBinarySign (term site) := by
  induction sites using Finset.induction_on with
  | empty => simp [realBinarySign]
  | insert site sites hsite ih =>
      rw [Finset.sum_insert hsite, Finset.prod_insert hsite,
        realBinarySign_add, ih]
theorem bernoulliCharacter_coordinate_sum (p : ErrorParameter)
    (codewordBit : ZMod 2) :
    (∑ errorBit : ZMod 2,
      (if errorBit = 0 then p.cleanWeight else p.rate) *
        realBinarySign (codewordBit * errorBit)) =
      if codewordBit = 0 then 1 else 1 - 2 * p.rate := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  by_cases hcodeword : codewordBit = 0
  · subst codewordBit
    simp [realBinarySign, ErrorParameter.cleanWeight]
  · have hcodewordOne := zmod_two_eq_one_of_ne_zero hcodeword
    subst codewordBit
    have hone_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
    simp [realBinarySign, ErrorParameter.cleanWeight, hone_ne_zero]
    ring
theorem hammingWeight_product_of_zero_one {q : Nat}
    (weight : ℝ) (word : PhysicalError q) :
    (∏ site, if word site = 0 then 1 else weight) =
      weight ^ HammingWeight word := by
  classical
  let support := hammingSupport word
  have hdisjoint : Disjoint support (Finset.univ \ support) := by
    exact Finset.disjoint_sdiff
  have hunion : support ∪ (Finset.univ \ support) = Finset.univ := by
    simp
  have hsupp_card : support.card = HammingWeight word := by
    rfl
  calc
    (∏ site, if word site = 0 then 1 else weight) =
        (∏ site ∈ support, if word site = 0 then 1 else weight) *
          ∏ site ∈ Finset.univ \ support, if word site = 0 then 1 else weight := by
      rw [← Finset.prod_union hdisjoint, hunion]
    _ = (∏ _site ∈ support, weight) *
          ∏ _site ∈ Finset.univ \ support, 1 := by
      congr 1
      · apply Finset.prod_congr rfl
        intro site hsite
        have hnonzero : word site ≠ 0 := by
          simpa [support, hammingSupport] using hsite
        simp [hnonzero]
      · apply Finset.prod_congr rfl
        intro site hsite
        have hzero : word site = 0 := by
          by_contra hnonzero
          exact (Finset.mem_sdiff.mp hsite).2
            (by simp [support, hammingSupport, hnonzero])
        simp [hzero]
    _ = weight ^ HammingWeight word := by
      simp [hsupp_card]
theorem bernoulliCharacter_transform (q : Nat) (p : ErrorParameter)
    (codeword : PhysicalError q) :
    (∑ error : PhysicalError q,
      errorWordProbability p error *
        realBinarySign (wordPairing codeword error)) =
      (1 - 2 * p.rate) ^ HammingWeight codeword := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := Column q) (κ := ZMod 2)
    (s := Finset.univ)
    (g := fun site errorBit =>
      (if errorBit = 0 then p.cleanWeight else p.rate) *
        realBinarySign (codeword site * errorBit))
  calc
    (∑ error : PhysicalError q,
      errorWordProbability p error *
        realBinarySign (wordPairing codeword error)) =
        ∑ error : PhysicalError q,
          ∏ site,
            (if error site = 0 then p.cleanWeight else p.rate) *
              realBinarySign (codeword site * error site) := by
      apply Finset.sum_congr rfl
      intro error _
      rw [errorWordProbability, wordPairing_apply, dotProduct,
        realBinarySign_sum_eq_prod, Finset.prod_mul_distrib]
    _ = ∏ site,
        ∑ errorBit : ZMod 2,
          (if errorBit = 0 then p.cleanWeight else p.rate) *
            realBinarySign (codeword site * errorBit) := by
      simpa using h
    _ = ∏ site, if codeword site = 0 then 1 else 1 - 2 * p.rate := by
      apply Finset.prod_congr rfl
      intro site _
      exact bernoulliCharacter_coordinate_sum p (codeword site)
    _ = (1 - 2 * p.rate) ^ HammingWeight codeword :=
      hammingWeight_product_of_zero_one (1 - 2 * p.rate) codeword
theorem evenCode_carrier_card (q : Nat) :
    Fintype.card (family q).evenCode.carrier = 8 := by
  calc
    Fintype.card (family q).evenCode.carrier =
        Fintype.card (EvenRow → ZMod 2) :=
      Fintype.card_congr (evenCoefficientLinearEquiv q).toEquiv.symm
    _ = Fintype.card (Fin 8) :=
      Fintype.card_congr coefficientEquiv.symm
    _ = 8 := Fintype.card_fin 8
theorem sum_dite_submodule_real
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype M] (S : Submodule R M) [Fintype S]
    [DecidablePred fun x : M => x ∈ S] (f : S → ℝ) :
    (∑ x : M, if hx : x ∈ S then f ⟨x, hx⟩ else 0) =
      ∑ x : S, f x := by
  classical
  let g : M → ℝ := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have h := Finset.sum_subtype (p := fun x : M => x ∈ S) (F := inferInstance)
    (Finset.univ.filter fun x : M => x ∈ S) (by simp) g
  have hsub :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x =
        ∑ x : S, f x := by
    simpa [g] using h
  have hall :
      ∑ x ∈ Finset.univ.filter (fun x : M => x ∈ S), g x =
        ∑ x : M, g x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _hx hxnot
    have hxS : x ∉ S := by simpa using hxnot
    simp [g, hxS]
  exact hall.symm.trans hsub
theorem sum_dite_evenCodeDual (q : Nat)
    (f : (family q).evenCode.dual.carrier → ℝ) :
    (∑ error : PhysicalError q,
      if herror : error ∈ (family q).evenCode.dual.carrier then
        f ⟨error, herror⟩ else 0) =
      ∑ error : (family q).evenCode.dual.carrier, f error := by
  exact sum_dite_submodule_real (family q).evenCode.dual.carrier f
theorem evenCode_dual_indicator_eq_character_average (q : Nat)
    (error : PhysicalError q) :
    (if error ∈ (family q).evenCode.dual.carrier then (1 : ℝ) else 0) =
      (8 : ℝ)⁻¹ *
        ∑ codeword : (family q).evenCode.carrier,
          evenCodeBinaryCharacter codeword error := by
  rw [evenCode_binaryCharacter_sum, evenCode_carrier_card]
  by_cases hdual : error ∈ (family q).evenCode.dual.carrier <;>
    simp only [hdual, if_true, if_false, Nat.cast_ofNat, Nat.cast_zero, mul_zero] <;>
      norm_num
theorem evenCode_dual_bernoulliMass_eq_weightSum (q : Nat)
    (p : ErrorParameter) :
    (∑ error : (family q).evenCode.dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
      (8 : ℝ)⁻¹ *
        codeWeightSum (family q).evenCode
          (fun weight => (1 - 2 * p.rate) ^ weight) := by
  classical
  calc
    (∑ error : (family q).evenCode.dual.carrier,
      errorWordProbability p (error : PhysicalError q)) =
        ∑ error : PhysicalError q,
          if herror : error ∈ (family q).evenCode.dual.carrier then
            errorWordProbability p error else 0 := by
      symm
      simpa using sum_dite_evenCodeDual q
        (fun error => errorWordProbability p (error : PhysicalError q))
    _ = ∑ error : PhysicalError q,
          errorWordProbability p error *
            (if error ∈ (family q).evenCode.dual.carrier then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases hdual : error ∈ (family q).evenCode.dual.carrier <;>
        simp only [hdual, dite_true, dite_false, if_true, if_false, mul_one, mul_zero]
    _ = ∑ error : PhysicalError q,
          errorWordProbability p error *
            ((8 : ℝ)⁻¹ *
              ∑ codeword : (family q).evenCode.carrier,
                evenCodeBinaryCharacter codeword error) := by
      apply Finset.sum_congr rfl
      intro error _
      rw [evenCode_dual_indicator_eq_character_average]
      apply congrArg (errorWordProbability p error * ·)
      apply congrArg ((8 : ℝ)⁻¹ * ·)
      apply Finset.sum_congr
      · ext codeword
        simp
      · intro codeword _
        rfl
    _ = (8 : ℝ)⁻¹ *
          ∑ codeword : (family q).evenCode.carrier,
            ∑ error : PhysicalError q,
              errorWordProbability p error *
                evenCodeBinaryCharacter codeword error := by
      calc
        (∑ error : PhysicalError q,
          errorWordProbability p error *
            ((8 : ℝ)⁻¹ *
              ∑ codeword : (family q).evenCode.carrier,
                evenCodeBinaryCharacter codeword error)) =
            ∑ error : PhysicalError q,
              ∑ codeword : (family q).evenCode.carrier,
                (8 : ℝ)⁻¹ *
                  (errorWordProbability p error *
                    evenCodeBinaryCharacter codeword error) := by
              apply Finset.sum_congr rfl
              intro error _
              calc
                errorWordProbability p error *
                    ((8 : ℝ)⁻¹ *
                      ∑ codeword : (family q).evenCode.carrier,
                        evenCodeBinaryCharacter codeword error) =
                    (8 : ℝ)⁻¹ *
                      (errorWordProbability p error *
                        ∑ codeword : (family q).evenCode.carrier,
                          evenCodeBinaryCharacter codeword error) := by
                  ring
                _ = (8 : ℝ)⁻¹ *
                      ∑ codeword : (family q).evenCode.carrier,
                        errorWordProbability p error *
                          evenCodeBinaryCharacter codeword error := by
                  rw [Finset.mul_sum]
                _ = ∑ codeword : (family q).evenCode.carrier,
                      (8 : ℝ)⁻¹ *
                        (errorWordProbability p error *
                          evenCodeBinaryCharacter codeword error) := by
                  rw [Finset.mul_sum]
        _ = (8 : ℝ)⁻¹ *
            ∑ codeword : (family q).evenCode.carrier,
              ∑ error : PhysicalError q,
                errorWordProbability p error *
                  evenCodeBinaryCharacter codeword error := by
              rw [Finset.sum_comm, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro codeword _
              rw [Finset.mul_sum]
    _ = (8 : ℝ)⁻¹ *
          ∑ codeword : (family q).evenCode.carrier,
            (1 - 2 * p.rate) ^ HammingWeight
              (codeword : PhysicalError q) := by
      apply congrArg
        ((8 : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro codeword _
      simpa [evenCodeBinaryCharacter] using
        bernoulliCharacter_transform q p (codeword : PhysicalError q)
    _ = (8 : ℝ)⁻¹ *
          codeWeightSum (family q).evenCode
            (fun weight => (1 - 2 * p.rate) ^ weight) := by
      apply congrArg ((8 : ℝ)⁻¹ * ·)
      unfold codeWeightSum
      apply Finset.sum_congr
      · ext codeword
        simp
      · intro codeword _
        rfl
theorem rawSuccessMass_eq_evenCode_weightSum (q : Nat)
    (p : ErrorParameter) :
    rawSuccessMass q p =
      (8 : ℝ)⁻¹ *
        codeWeightSum (family q).evenCode
          (fun weight => (1 - 2 * p.rate) ^ weight) := by
  classical
  rw [rawSuccessMass]
  calc
    (∑ error : PhysicalError q,
      if Accepts error then errorWordProbability p error else 0) =
        ∑ error : PhysicalError q,
          if herror : error ∈ (family q).evenCode.dual.carrier then
            errorWordProbability p
              ((⟨error, herror⟩ : (family q).evenCode.dual.carrier) :
                PhysicalError q)
          else 0 := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases hdual : error ∈ (family q).evenCode.dual.carrier <;>
        simp only [accepts_iff_mem_evenCode_dual, hdual,
          dite_true, dite_false, if_true, if_false]
    _ = ∑ error : (family q).evenCode.dual.carrier,
          errorWordProbability p (error : PhysicalError q) :=
      sum_dite_evenCodeDual q
        (fun error => errorWordProbability p (error : PhysicalError q))
    _ = (8 : ℝ)⁻¹ *
          codeWeightSum (family q).evenCode
            (fun weight => (1 - 2 * p.rate) ^ weight) :=
      evenCode_dual_bernoulliMass_eq_weightSum q p
theorem rawSuccessMass_eq_evenFamilyWeightSum (q : Nat)
    (p : ErrorParameter) :
    rawSuccessMass q p =
      (8 : ℝ)⁻¹ *
        (1 + (1 - 2 * p.rate) ^ 8 +
          6 * (1 - 2 * p.rate) ^ (4 + 4 * q)) := by
  rw [rawSuccessMass_eq_evenCode_weightSum, evenCode_weightSum]
  simp [nsmul_eq_mul]
def rawRejectMass (q : Nat) (p : ErrorParameter) : ℝ :=
  ∑ error : PhysicalError q,
    if Accepts error then 0 else errorWordProbability p error
def ambientEncodingIsometry (q : Nat) :
    LogicalRegister q →ₗᵢ[Complex] PhysicalRegister q :=
  (family q).cssQuantumCode.carrier.subtypeₗᵢ.comp
    ((family q).encoding (isTriorthogonal q)).toLinearIsometry
@[simp] theorem ambientEncodingIsometry_apply (q : Nat)
    (psi : LogicalRegister q) :
    ambientEncodingIsometry q psi =
      ((family q).encoding (isTriorthogonal q) psi : PhysicalRegister q) :=
  rfl
def codeDecoderBranch (q : Nat) :
    PhysicalRegister q →ₗ[Complex] LogicalRegister q :=
  LinearMap.adjoint (ambientEncodingIsometry q).toLinearMap
@[simp] theorem codeDecoderBranch_encoded (q : Nat)
    (psi : LogicalRegister q) :
    codeDecoderBranch q (ambientEncodingIsometry q psi) = psi := by
  change LinearMap.adjoint (ambientEncodingIsometry q).toLinearMap
    ((ambientEncodingIsometry q).toLinearMap psi) = psi
  exact LinearMap.congr_fun (ambientEncodingIsometry q).adjoint_comp_self' psi
theorem adjoint_codeDecoderBranch (q : Nat) :
    LinearMap.adjoint (codeDecoderBranch q) =
      (ambientEncodingIsometry q).toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]
def decoderCodeProjector (q : Nat) : Operator (PhysicalRegister q) :=
  (LinearMap.adjoint (codeDecoderBranch q)).comp (codeDecoderBranch q)
@[simp] theorem decoderCodeProjector_encoded (q : Nat)
    (psi : LogicalRegister q) :
    decoderCodeProjector q (ambientEncodingIsometry q psi) =
      ambientEncodingIsometry q psi := by
  change LinearMap.adjoint (codeDecoderBranch q)
    (codeDecoderBranch q (ambientEncodingIsometry q psi)) =
      ambientEncodingIsometry q psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl
theorem codeDecoderBranch_comp_adjoint (q : Nat) :
    (codeDecoderBranch q).comp
        (LinearMap.adjoint (codeDecoderBranch q)) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact (ambientEncodingIsometry q).adjoint_comp_self'
theorem decoderCodeProjector_idempotent (q : Nat) :
    (decoderCodeProjector q).comp (decoderCodeProjector q) =
      decoderCodeProjector q := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint (codeDecoderBranch q)).comp (codeDecoderBranch q)).comp
        ((LinearMap.adjoint (codeDecoderBranch q)).comp (codeDecoderBranch q)) =
        (LinearMap.adjoint (codeDecoderBranch q)).comp
          (((codeDecoderBranch q).comp
            (LinearMap.adjoint (codeDecoderBranch q))).comp
              (codeDecoderBranch q)) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint (codeDecoderBranch q)).comp
          ((1 : Operator (LogicalRegister q)).comp (codeDecoderBranch q)) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint (codeDecoderBranch q)).comp
          (codeDecoderBranch q) := by
            ext psi
            rfl
theorem decoderCodeProjector_adjoint (q : Nat) :
    LinearMap.adjoint (decoderCodeProjector q) = decoderCodeProjector q := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]
def decoderComplementProjector (q : Nat) : Operator (PhysicalRegister q) :=
  1 - decoderCodeProjector q
theorem decoderComplementProjector_adjoint (q : Nat) :
    LinearMap.adjoint (decoderComplementProjector q) =
      decoderComplementProjector q := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]
theorem decoderComplementProjector_idempotent (q : Nat) :
    (decoderComplementProjector q).comp (decoderComplementProjector q) =
      decoderComplementProjector q := by
  ext psi
  have hprojector := LinearMap.congr_fun
    (decoderCodeProjector_idempotent q) psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp] theorem decoderComplementProjector_encoded (q : Nat)
    (psi : LogicalRegister q) :
    decoderComplementProjector q (ambientEncodingIsometry q psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf
def decoderFallbackState (q : Nat) : LogicalRegister q :=
  BinaryRowFamily.logicalComputationalState (fun _ => 0)
theorem decoderFallbackState_inner_self (q : Nat) :
    inner Complex (decoderFallbackState q) (decoderFallbackState q) = 1 := by
  simp [decoderFallbackState, BinaryRowFamily.logicalComputationalState]
theorem decoderFallbackState_normSq (q : Nat) :
    ‖decoderFallbackState q‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    decoderFallbackState_inner_self]
  norm_num
noncomputable def decoderPhysicalBasis (q : Nat) :=
  stdOrthonormalBasis Complex (PhysicalRegister q)
def complementDecoderBranch (q : Nat)
    (i : Fin (Module.finrank Complex (PhysicalRegister q))) :
    PhysicalRegister q →ₗ[Complex] LogicalRegister q :=
  (InnerProductSpace.rankOne Complex (decoderFallbackState q)
    (decoderComplementProjector q (decoderPhysicalBasis q i))).toLinearMap
theorem complementDecoderBranch_adjoint_comp (q : Nat)
    (i : Fin (Module.finrank Complex (PhysicalRegister q))) :
    (LinearMap.adjoint (complementDecoderBranch q i)).comp
        (complementDecoderBranch q i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector q (decoderPhysicalBasis q i))
        (decoderComplementProjector q (decoderPhysicalBasis q i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex (decoderFallbackState q)
        (decoderComplementProjector q (decoderPhysicalBasis q i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector q (decoderPhysicalBasis q i))
        (decoderFallbackState q)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (decoderFallbackState q)
      (decoderComplementProjector q (decoderPhysicalBasis q i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState q‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq q
  simp [LinearMap.comp_apply, hnormSq]
theorem sum_complementDecoderBranch_adjoint_comp (q : Nat) :
    ∑ i : Fin (Module.finrank Complex (PhysicalRegister q)),
        (LinearMap.adjoint (complementDecoderBranch q i)).comp
          (complementDecoderBranch q i) = decoderComplementProjector q := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i,
        (InnerProductSpace.rankOne Complex
          (decoderComplementProjector q (decoderPhysicalBasis q i))
          (decoderComplementProjector q (decoderPhysicalBasis q i))).toLinearMap) =
        (decoderComplementProjector q).comp
          (LinearMap.adjoint (decoderComplementProjector q)) :=
      by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← (decoderPhysicalBasis q).sum_repr'
          (LinearMap.adjoint (decoderComplementProjector q) psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = (decoderComplementProjector q).comp
          (decoderComplementProjector q) := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector q :=
      decoderComplementProjector_idempotent q
def decoderKrausFamily (q : Nat) :
    FiniteKrausFamily
      (Sum Unit (Fin (Module.finrank Complex (PhysicalRegister q))))
      (PhysicalRegister q) (LogicalRegister q) where
  operator
    | .inl _ => codeDecoderBranch q
    | .inr i => complementDecoderBranch q i
theorem decoderKrausFamily_complete (q : Nat) :
    (decoderKrausFamily q).Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector q) +
      (∑ i : Fin (Module.finrank Complex (PhysicalRegister q)),
        (LinearMap.adjoint (complementDecoderBranch q i)).comp
          (complementDecoderBranch q i)) = 1
  rw [Fintype.sum_unique]
  rw [sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]
def decoderChannel (q : Nat) :
    QuantumChannel (PhysicalRegister q) (LogicalRegister q) :=
  (decoderKrausFamily q).toQuantumChannel (decoderKrausFamily_complete q)
def resourceCount (q : Nat) : Nat := Fintype.card (Column q)
@[simp] theorem resourceCount_eq_three_logicalCount_add_eight (q : Nat) :
    resourceCount q = 3 * logicalCount q + 8 :=
  card_column q
noncomputable def resourceSiteEquiv (q : Nat) :
    Column q ≃ Fin (resourceCount q) :=
  Fintype.equivFin (Column q)
def noisyResources (q : Nat) (p : ErrorParameter) :
    ResourceInput (resourceCount q) Qubit.QubitSpace :=
  fun _ => OneQubit.diagonalAResource p
def resourceOutcome (bit : ZMod 2) : StabilizerOutcome :=
  if bit = 0 then .positive else .negative
def measuredErrorWordProbability (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (error : PhysicalError q) : ℝ :=
  ∏ site, OneQubit.aBasisInstrument.bornWeight
    (resourceOutcome (error site)) (inputs (resourceSiteEquiv q site))
theorem measuredErrorWordProbability_nonneg (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (error : PhysicalError q) :
    0 ≤ measuredErrorWordProbability q inputs error := by
  apply Finset.prod_nonneg
  intro site _
  exact OneQubit.aBasisInstrument_weight_nonneg _ _
theorem sum_measuredErrorWordProbability (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    ∑ error : PhysicalError q,
      measuredErrorWordProbability q inputs error = 1 := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := Column q) (κ := ZMod 2)
    (s := Finset.univ)
    (g := fun site bit => OneQubit.aBasisInstrument.bornWeight
      (resourceOutcome bit) (inputs (resourceSiteEquiv q site)))
  have hsite (site : Column q) :
      ∑ bit : ZMod 2, OneQubit.aBasisInstrument.bornWeight
        (resourceOutcome bit) (inputs (resourceSiteEquiv q site)) = 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simpa [resourceOutcome] using
      OneQubit.aBasisInstrument_weight_sum
        (inputs (resourceSiteEquiv q site))
  simp_rw [hsite] at h
  simpa [measuredErrorWordProbability] using h
theorem measuredErrorWordProbability_noisyResources (q : Nat)
    (p : ErrorParameter) (error : PhysicalError q) :
    measuredErrorWordProbability q (noisyResources q p) error =
      errorWordProbability p error := by
  apply Finset.prod_congr rfl
  intro site _
  by_cases herror : error site = 0
  · simp [noisyResources, resourceOutcome, herror,
      OneQubit.aBasisInstrument_diagonalAResource_weight]
  · simp [noisyResources, resourceOutcome, herror,
      OneQubit.aBasisInstrument_diagonalAResource_weight]
def errorWordBasisState {q : Nat} (error : PhysicalError q) :
    PhysicalRegister q :=
  EuclideanSpace.basisFun (Qubit.Bitstring (Column q)) Complex
    ((bitstringWordEquiv (Column q)).symm error)
theorem errorWordBasisState_normSq {q : Nat} (error : PhysicalError q) :
    ‖errorWordBasisState error‖ ^ 2 = 1 := by
  simp [errorWordBasisState]
def errorWordBasisDensity {q : Nat} (error : PhysicalError q) :
    DensityOperator (PhysicalRegister q) :=
  DensityOperator.pureDensity (errorWordBasisState error)
    (errorWordBasisState_normSq error)
noncomputable def errorWordBasis (q : Nat) :
    OrthonormalBasis (PhysicalError q) Complex (PhysicalRegister q) :=
  (EuclideanSpace.basisFun (Qubit.Bitstring (Column q)) Complex).reindex
    (bitstringWordEquiv (Column q))
@[simp] theorem errorWordBasis_apply (q : Nat) (error : PhysicalError q) :
    errorWordBasis q error = errorWordBasisState error := by
  simp [errorWordBasis, errorWordBasisState]
def prepareMeasuredResources (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    DensityOperator (PhysicalRegister q) :=
  DensityOperator.convexCombination Finset.univ
    (measuredErrorWordProbability q inputs)
    errorWordBasisDensity
    (fun error _ => measuredErrorWordProbability_nonneg q inputs error)
    (sum_measuredErrorWordProbability q inputs)
@[simp] theorem prepareMeasuredResources_toOperator (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    (prepareMeasuredResources q inputs).toOperator =
      ∑ error : PhysicalError q,
        (measuredErrorWordProbability q inputs error : Complex) •
          (errorWordBasisDensity error).toOperator := by
  simp [prepareMeasuredResources,
    DensityOperator.convexCombinationOperator]
def resourceConsumerKrausFamily (q : Nat) :
    FiniteKrausFamily (PhysicalError q)
      (PhysicalRegister q) (PhysicalRegister q) where
  operator error :=
    (InnerProductSpace.rankOne Complex
      (errorBranchState error) (errorWordBasisState error)).toLinearMap
theorem resourceConsumerKrausFamily_adjoint_comp (q : Nat)
    (error : PhysicalError q) :
    (LinearMap.adjoint ((resourceConsumerKrausFamily q).operator error)).comp
        ((resourceConsumerKrausFamily q).operator error) =
      (InnerProductSpace.rankOne Complex
        (errorWordBasisState error) (errorWordBasisState error)).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex
        (errorBranchState error) (errorWordBasisState error)).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (errorWordBasisState error) (errorBranchState error)).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex
      (errorBranchState error) (errorWordBasisState error)).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  ext psi
  simp only [resourceConsumerKrausFamily]
  rw [hadjoint]
  have hnormSq : (↑‖errorBranchState error‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact errorBranchState_normSq error
  simp [LinearMap.comp_apply, hnormSq]
theorem resourceConsumerKrausFamily_complete (q : Nat) :
    (resourceConsumerKrausFamily q).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp_rw [resourceConsumerKrausFamily_adjoint_comp]
  have hcomplete := congrArg ContinuousLinearMap.toLinearMap
    (OrthonormalBasis.sum_rankOne_eq_id (errorWordBasis q))
  simp only [errorWordBasis_apply, ContinuousLinearMap.toLinearMap_sum] at hcomplete
  exact hcomplete
def resourceConsumerChannel (q : Nat) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  (resourceConsumerKrausFamily q).toQuantumChannel
    (resourceConsumerKrausFamily_complete q)
theorem resourceConsumerBranch_basis (q : Nat)
    (error observed : PhysicalError q) :
    (resourceConsumerKrausFamily q).operator error
        (errorWordBasisState observed) =
      if error = observed then errorBranchState error else 0 := by
  classical
  simp only [resourceConsumerKrausFamily]
  change inner Complex (errorWordBasisState error) (errorWordBasisState observed) •
      errorBranchState error = _
  rw [← errorWordBasis_apply q error, ← errorWordBasis_apply q observed]
  rw [(errorWordBasis q).inner_eq_ite]
  simp
noncomputable def resourceConsumerBranchMap (q : Nat)
    (error : PhysicalError q) :
    Operator (PhysicalRegister q) →ₗ[Complex] Operator (PhysicalRegister q) where
  toFun := fun A =>
    (resourceConsumerKrausFamily q).operator error |>.comp
      (A.comp (LinearMap.adjoint ((resourceConsumerKrausFamily q).operator error)))
  map_add' := by
    intro A B
    ext psi
    simp [LinearMap.comp_apply, map_add]
  map_smul' := by
    intro scalar A
    ext psi
    simp [LinearMap.comp_apply, map_smul]
theorem resourceConsumerBranchMap_errorWordBasisDensity (q : Nat)
    (error observed : PhysicalError q) :
    resourceConsumerBranchMap q error (errorWordBasisDensity observed).toOperator =
      if error = observed then (errorBranchDensity error).toOperator else 0 := by
  change ((resourceConsumerKrausFamily q).operator error).comp
      ((errorWordBasisDensity observed).toOperator.comp
        (LinearMap.adjoint ((resourceConsumerKrausFamily q).operator error))) = _
  rw [errorWordBasisDensity, DensityOperator.pureDensity_toOperator, sandwich_rankOne,
    resourceConsumerBranch_basis]
  by_cases h : error = observed <;> simp [h, errorBranchDensity,
    DensityOperator.pureDensity_toOperator]
theorem resourceConsumerChannel_prepares_branchMixture (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    resourceConsumerChannel q (prepareMeasuredResources q inputs).toOperator =
      ∑ error : PhysicalError q,
        (measuredErrorWordProbability q inputs error : Complex) •
          (errorBranchDensity error).toOperator := by
  rw [resourceConsumerChannel,
    FiniteKrausFamily.toQuantumChannel_apply_sum,
    prepareMeasuredResources_toOperator]
  change ∑ error : PhysicalError q,
      resourceConsumerBranchMap q error
        (∑ observed : PhysicalError q,
          (measuredErrorWordProbability q inputs observed : Complex) •
            (errorWordBasisDensity observed).toOperator) = _
  simp_rw [map_sum, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro observed _
  rw [← Finset.smul_sum]
  apply congrArg
  rw [Fintype.sum_eq_single observed]
  · rw [resourceConsumerBranchMap_errorWordBasisDensity]
    simp
  · intro error hne
    rw [resourceConsumerBranchMap_errorWordBasisDensity]
    simp [hne]
theorem resourceConsumer_noisyResources_eq_preSyndromeState (q : Nat)
    (p : ErrorParameter) :
    (resourceConsumerChannel q).mapDensity
        (prepareMeasuredResources q (noisyResources q p)) =
      preSyndromeState q p := by
  apply DensityOperator.ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator,
    resourceConsumerChannel_prepares_branchMixture,
    preSyndromeState_toOperator]
  apply Finset.sum_congr rfl
  intro error _
  rw [measuredErrorWordProbability_noisyResources]
def resourcePreSyndromeState (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    DensityOperator (PhysicalRegister q) :=
  (resourceConsumerChannel q).mapDensity (prepareMeasuredResources q inputs)
theorem resourcePreSyndromeState_noisyResources (q : Nat)
    (p : ErrorParameter) :
    resourcePreSyndromeState q (noisyResources q p) = preSyndromeState q p :=
  resourceConsumer_noisyResources_eq_preSyndromeState q p
def resourceEndpoint (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome) : Operator (PhysicalRegister q) :=
  (protocolSyndromeInstrument q).branchOperator outcome
    (resourcePreSyndromeState q inputs).toOperator
def resourceEndpointWeight (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome) : ℝ :=
  (protocolSyndromeInstrument q).bornWeight outcome (resourcePreSyndromeState q inputs)
theorem resourceEndpointWeight_noisyResources (q : Nat)
    (p : ErrorParameter) (outcome : DistillationOutcome) :
    resourceEndpointWeight q (noisyResources q p) outcome = endpointWeight q p outcome := by
  unfold resourceEndpointWeight endpointWeight
  rw [resourcePreSyndromeState_noisyResources]
def resourceEndpointConditional (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < resourceEndpointWeight q inputs outcome) :
    DensityOperator (PhysicalRegister q) :=
  (protocolSyndromeInstrument q).conditionalDensity outcome
    (resourcePreSyndromeState q inputs) hpos
@[simp] theorem resourceEndpointConditional_toOperator (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < resourceEndpointWeight q inputs outcome) :
    (resourceEndpointConditional q inputs outcome hpos).toOperator =
      ((resourceEndpointWeight q inputs outcome : Complex)⁻¹) •
        resourceEndpoint q inputs outcome :=
  rfl
theorem resourceEndpointWeight_nonneg (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome) :
    0 ≤ resourceEndpointWeight q inputs outcome :=
  (protocolSyndromeInstrument q).bornWeight_nonneg outcome
    (resourcePreSyndromeState q inputs)
theorem resourceEndpointWeight_sum (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    resourceEndpointWeight q inputs .accepted +
      resourceEndpointWeight q inputs .rejected = 1 := by
  have h := (protocolSyndromeInstrument q).sum_bornWeight_eq_one
    (protocolSyndromeInstrument_complete q) (resourcePreSyndromeState q inputs)
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at h
  simpa [resourceEndpointWeight] using h
theorem resourceEndpoint_eq_zero_of_weight_eq_zero (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome)
    (hzero : resourceEndpointWeight q inputs outcome = 0) :
    resourceEndpoint q inputs outcome = 0 :=
  (protocolSyndromeInstrument q).branchOperator_eq_zero_of_bornWeight_eq_zero
    outcome (resourcePreSyndromeState q inputs) hzero
def resourceEndpointFallback (q : Nat) : DensityOperator (PhysicalRegister q) :=
  errorBranchDensity 0
noncomputable def resourceEndpointCompletion (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome) : DensityOperator (PhysicalRegister q) :=
  if hpos : 0 < resourceEndpointWeight q inputs outcome then
    resourceEndpointConditional q inputs outcome hpos
  else resourceEndpointFallback q
theorem resourceEndpointWeight_smul_completion_toOperator (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (outcome : DistillationOutcome) :
    (resourceEndpointWeight q inputs outcome : Complex) •
        (resourceEndpointCompletion q inputs outcome).toOperator =
      resourceEndpoint q inputs outcome := by
  classical
  by_cases hpos : 0 < resourceEndpointWeight q inputs outcome
  · rw [resourceEndpointCompletion, dif_pos hpos]
    simpa [resourceEndpointWeight, resourceEndpointConditional, resourceEndpoint] using
      (protocolSyndromeInstrument q).bornWeight_smul_conditionalDensity_toOperator outcome
          (resourcePreSyndromeState q inputs) hpos
  · rw [resourceEndpointCompletion, dif_neg hpos]
    have hzero : resourceEndpointWeight q inputs outcome = 0 :=
      le_antisymm (not_lt.mp hpos)
        (resourceEndpointWeight_nonneg q inputs outcome)
    rw [hzero, resourceEndpoint_eq_zero_of_weight_eq_zero q inputs outcome hzero]
    simp
def resourceAcceptedOutput (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (hpos : 0 < resourceEndpointWeight q inputs .accepted) :
    DensityOperator (LogicalRegister q) :=
  (decoderChannel q).mapDensity
    (resourceEndpointConditional q inputs .accepted hpos)
def resourceSyndromeOperation (q : Nat) :
    QuantumChannel (PhysicalRegister q) (PhysicalRegister q) :=
  QuantumChannel.comp (syndromeMeasurementChannel q)
    (resourceConsumerChannel q)
theorem resourceSyndromeOperation_output_decomposition (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    (resourceSyndromeOperation q).mapDensity
        (prepareMeasuredResources q inputs) =
      outcomeMixture (resourceEndpointWeight q inputs .accepted)
        (resourceEndpointWeight_nonneg q inputs .accepted)
        (by
          have hsum := resourceEndpointWeight_sum q inputs
          linarith [resourceEndpointWeight_nonneg q inputs .rejected])
        (resourceEndpointCompletion q inputs .accepted)
        (resourceEndpointCompletion q inputs .rejected) := by
  apply DensityOperator.ext_toOperator
  rw [resourceSyndromeOperation, QuantumChannel.comp_mapDensity]
  change (((protocolSyndromeInstrument q).kraus.toQuantumChannel
      (protocolSyndromeInstrument_complete q)).mapDensity
        (resourcePreSyndromeState q inputs)).toOperator = _
  rw [← (protocolSyndromeInstrument q).sum_branchOperator_eq_mapDensity_toOperator
      (protocolSyndromeInstrument_complete q) (resourcePreSyndromeState q inputs)]
  change (∑ outcome, resourceEndpoint q inputs outcome) = _
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide]
  have hreject : 1 - resourceEndpointWeight q inputs .accepted =
      resourceEndpointWeight q inputs .rejected := by
    linarith [resourceEndpointWeight_sum q inputs]
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide,
    hreject]
  rw [← resourceEndpointWeight_smul_completion_toOperator q inputs .accepted,
    ← resourceEndpointWeight_smul_completion_toOperator q inputs .rejected]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  rfl
noncomputable def resourceSyndromeRun (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    DistillationRun Qubit.QubitSpace (PhysicalRegister q) (PhysicalRegister q) where
  resourceCount := resourceCount q
  noisyInput := inputs
  prepareInput := prepareMeasuredResources q
  operation := resourceSyndromeOperation q
  successProbability := resourceEndpointWeight q inputs .accepted
  success_nonneg := resourceEndpointWeight_nonneg q inputs .accepted
  success_le_one := by
    have hsum := resourceEndpointWeight_sum q inputs
    linarith [resourceEndpointWeight_nonneg q inputs .rejected]
  acceptedOutput := resourceEndpointCompletion q inputs .accepted
  rejectedOutput := resourceEndpointCompletion q inputs .rejected
  output_decomposition := resourceSyndromeOperation_output_decomposition q inputs
def decodedOperation (q : Nat) :
    QuantumChannel (PhysicalRegister q) (LogicalRegister q) :=
  QuantumChannel.comp (decoderChannel q)
    (QuantumChannel.comp (syndromeMeasurementChannel q)
      (resourceConsumerChannel q))
noncomputable def resourceDecodedRun (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    DistillationRun Qubit.QubitSpace (PhysicalRegister q) (LogicalRegister q) :=
  (resourceSyndromeRun q inputs).postprocess (decoderChannel q)
def logicalErrorWord {q : Nat} (error : PhysicalError q) :
    Word (ZMod 2) (OddRow q) :=
  fun logical => wordPairing error (oddWord logical)
def rawLogicalErrorWeight (q : Nat) (p : ErrorParameter)
    (logical : Word (ZMod 2) (OddRow q)) : ℝ :=
  ∑ error : PhysicalError q,
    if Accepts error ∧ logicalErrorWord error = logical
      then errorWordProbability p error else 0
def rawMarginalErrorWeight (q : Nat) (p : ErrorParameter) (a : OddRow q) : ℝ :=
  ∑ logical : Word (ZMod 2) (OddRow q),
    if logical a = 0 then 0 else rawLogicalErrorWeight q p logical
def decodedMarginalError (q : Nat) (p : ErrorParameter)
    (hpos : 0 < rawSuccessMass q p) (a : OddRow q) : ℝ :=
  if h : 0 < rawSuccessMass q p then
    rawMarginalErrorWeight q p a / rawSuccessMass q p
  else (h hpos).elim
noncomputable def rowCodeDualCosetBernoulliMass (q : Nat) (p : ErrorParameter)
    (logical : Word (ZMod 2) (OddRow q)) : ℝ := by
  classical
  exact ∑ error : PhysicalError q,
    if error - (family q).oddCombination logical ∈
        (family q).rowCode.dual.carrier then
      errorWordProbability p error else 0
noncomputable instance binaryCodeDualMembershipDecidable {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) :
    DecidablePred (fun error : PhysicalError q => error ∈ C.dual.carrier) :=
  Classical.decPred _
def binaryCodeTranslate {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) (word : C.carrier) :
    C.carrier ≃ C.carrier where
  toFun := fun codeword => codeword + word
  invFun := fun codeword => codeword - word
  left_inv := by
    intro codeword
    exact add_sub_cancel_right codeword word
  right_inv := by
    intro codeword
    exact sub_add_cancel codeword word
@[simp] theorem coe_binaryCodeTranslate_apply {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) (word codeword : C.carrier) :
    ((binaryCodeTranslate C word codeword : C.carrier) : PhysicalError q) =
      (codeword : PhysicalError q) + (word : PhysicalError q) :=
  rfl
def binaryCodeCharacter {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) (codeword : C.carrier)
    (error : PhysicalError q) : ℝ :=
  realBinarySign (wordPairing (codeword : PhysicalError q) error)
noncomputable def binaryCodeCarrierCard {q : Nat}
    (C : LinearCode (ZMod 2) (Column q)) : Nat :=
  letI : Fintype C.carrier := Fintype.ofFinite _
  Fintype.card C.carrier
theorem rawSuccessMass_one_eighth_le_of_rate_le_half (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) :
    (8 : ℝ)⁻¹ ≤ rawSuccessMass q p := by
  let r : ℝ := 1 - 2 * p.rate
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith
  have hsum : 1 ≤ 1 + r ^ 8 + 6 * r ^ (4 + 4 * q) := by
    have h8 : 0 ≤ r ^ 8 := pow_nonneg hr0 _
    have hlong : 0 ≤ r ^ (4 + 4 * q) := pow_nonneg hr0 _
    linarith
  rw [rawSuccessMass_eq_evenFamilyWeightSum]
  change (8 : ℝ)⁻¹ ≤
    (8 : ℝ)⁻¹ * (1 + r ^ 8 + 6 * r ^ (4 + 4 * q))
  calc
    (8 : ℝ)⁻¹ = (8 : ℝ)⁻¹ * 1 := by ring
    _ ≤ (8 : ℝ)⁻¹ * (1 + r ^ 8 + 6 * r ^ (4 + 4 * q)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
theorem rawSuccessMass_pos_of_rate_le_half (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) :
    0 < rawSuccessMass q p := by
  exact lt_of_lt_of_le (by norm_num)
    (rawSuccessMass_one_eighth_le_of_rate_le_half q p hhalf)
def bh12IndependentInputModel (q : Nat) (p : ErrorParameter) :
    IndependentInputErrorModel (resourceCount q) Qubit.QubitSpace where
  rate := fun _ => p.rate
  rate_nonneg := fun _ => p.rate_nonneg
  rate_le_one := fun _ => p.rate_le_one
  admissible := fun rates inputs =>
    ∀ site, rates site = p.rate ∧
      inputs site = OneQubit.diagonalAResource p
theorem bh12IndependentInputModel_permits (q : Nat) (p : ErrorParameter) :
    (InputErrorModel.independent (bh12IndependentInputModel q p)).Permits
      (noisyResources q p) := by
  change ∀ site, (fun _ => p.rate) site = p.rate ∧
    noisyResources q p site = OneQubit.diagonalAResource p
  intro site
  exact ⟨rfl, rfl⟩
noncomputable def bh12IdealOutput (q : Nat) : DensityOperator (LogicalRegister q) :=
  DensityOperator.pureDensity
    (BinaryRowFamily.logicalMagicState (OddRow q))
    (by
      have hinner :
          inner Complex
              (BinaryRowFamily.logicalMagicState (OddRow q))
              (BinaryRowFamily.logicalMagicState (OddRow q)) = 1 := by
        exact BinaryRowFamily.logicalMagicState_inner_self (OddRow q)
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
      norm_num)
noncomputable def logicalABasisObservable {q : Nat} (a : OddRow q) :
    Operator (LogicalRegister q) :=
  (allSiteT (Index := OddRow q)).conjOperator (Qubit.localX a)
noncomputable def logicalABasisProjector {q : Nat} (a : OddRow q)
    (outcome : StabilizerOutcome) : Operator (LogicalRegister q) :=
  (1 / 2 : Complex) •
    (1 + outcome.sign • logicalABasisObservable a)
noncomputable def logicalABasisKrausFamily {q : Nat} (a : OddRow q) :
    FiniteKrausFamily StabilizerOutcome (LogicalRegister q) (LogicalRegister q) where
  operator := logicalABasisProjector a
noncomputable def logicalABasisInstrument {q : Nat} (a : OddRow q) :
    FiniteInstrument StabilizerOutcome StabilizerOutcome
      (LogicalRegister q) (LogicalRegister q) where
  kraus := logicalABasisKrausFamily a
  observe := id
theorem logical_wordPairing_single_left {q : Nat} (a : OddRow q)
    (logical : Word (ZMod 2) (OddRow q)) :
    wordPairing (Pi.single a 1) logical = logical a := by
  classical
  rw [wordPairing_apply, dotProduct, Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · simp
theorem logicalXOperator_eq_localX {q : Nat} (a : OddRow q) :
    toQubitOperator (cssXCheck (Pi.single a 1)) = Qubit.localX a := by
  classical
  have hsupport : binarySupport (Pi.single a 1) = {a} := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [binarySupport]
    · simp [binarySupport, hxa]
  ext psi bits
  simp [toQubitOperator_apply, cssXCheck, xSupport, zSupport,
    hsupport, Qubit.flipSupport_singleton, Qubit.zSupportPhase]
theorem allSiteT_commutes_logicalZ {q : Nat}
    (logical : Word (ZMod 2) (OddRow q)) (psi : LogicalRegister q) :
    (allSiteT (Index := OddRow q))
        (toQubitOperator (cssZCheck logical) psi) =
      toQubitOperator (cssZCheck logical)
        ((allSiteT (Index := OddRow q)) psi) := by
  ext bits
  simp only [allSiteT_apply, toQubitOperator_apply]
  simp [xSupport, zSupport, binarySupport]
  ring
theorem localX_logicalPlusState {q : Nat} (a : OddRow q) :
    Qubit.localX a (BinaryRowFamily.logicalPlusState (OddRow q)) =
      BinaryRowFamily.logicalPlusState (OddRow q) := by
  ext bits
  simp [BinaryRowFamily.logicalPlusState_apply]
noncomputable def logicalErrorState {q : Nat}
    (logical : Word (ZMod 2) (OddRow q)) : LogicalRegister q :=
  toQubitOperator (cssZCheck logical)
    (BinaryRowFamily.logicalMagicState (OddRow q))
theorem logicalErrorState_normSq {q : Nat}
    (logical : Word (ZMod 2) (OddRow q)) :
    ‖logicalErrorState logical‖ ^ 2 = 1 := by
  have hinner :
      inner Complex (logicalErrorState logical) (logicalErrorState logical) = 1 := by
    simp only [logicalErrorState]
    rw [← LinearMap.adjoint_inner_left]
    have hunit := toQubitOperator_adjoint_comp_self (cssZCheck logical)
    have happ :
        LinearMap.adjoint (toQubitOperator (cssZCheck logical))
            (toQubitOperator (cssZCheck logical)
              (BinaryRowFamily.logicalMagicState (OddRow q))) =
          BinaryRowFamily.logicalMagicState (OddRow q) := by
      have := LinearMap.congr_fun hunit
        (BinaryRowFamily.logicalMagicState (OddRow q))
      simpa [LinearMap.comp_apply] using this
    rw [happ]
    exact BinaryRowFamily.logicalMagicState_inner_self (OddRow q)
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner]
  norm_num
@[simp] theorem logicalErrorState_zero {q : Nat} :
    logicalErrorState (0 : Word (ZMod 2) (OddRow q)) =
      BinaryRowFamily.logicalMagicState (OddRow q) := by
  ext bits
  simp [logicalErrorState, toQubitOperator_apply, cssZCheck, xSupport,
    zSupport, binaryPhaseScalar, Qubit.zSupportPhase]
@[simp] theorem logicalABasisObservable_logicalMagicState {q : Nat}
    (a : OddRow q) :
    logicalABasisObservable a
        (BinaryRowFamily.logicalMagicState (OddRow q)) =
      BinaryRowFamily.logicalMagicState (OddRow q) := by
  rw [← allSiteT_logicalPlusState q]
  rw [logicalABasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [localX_logicalPlusState]
theorem localX_logicalZ_relation {q : Nat} (a : OddRow q)
    (logical : Word (ZMod 2) (OddRow q)) :
    Qubit.localX a * toQubitOperator (cssZCheck logical) =
      if logical a = 0 then
        toQubitOperator (cssZCheck logical) * Qubit.localX a
      else
        -(toQubitOperator (cssZCheck logical) * Qubit.localX a) := by
  rw [← logicalXOperator_eq_localX a]
  by_cases hbit : logical a = 0
  · rw [if_pos hbit]
    exact cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
      (by simpa [logical_wordPairing_single_left] using hbit)
  · rw [if_neg hbit]
    apply toQubitOperator_anticommute_of_not_commutes
    have hpair : wordPairing (Pi.single a 1) logical ≠ 0 := by
      simpa [logical_wordPairing_single_left] using hbit
    simpa [cssXCheck, cssZCheck, Commutes,
      symplecticForm_x_zero_zero_z_eq_wordPairing] using hpair
theorem logicalABasisObservable_logicalErrorState {q : Nat} (a : OddRow q)
    (logical : Word (ZMod 2) (OddRow q)) :
    logicalABasisObservable a (logicalErrorState logical) =
      if logical a = 0 then logicalErrorState logical
      else -logicalErrorState logical := by
  rw [logicalErrorState, ← allSiteT_logicalPlusState q]
  rw [logicalABasisObservable, UnitaryTransport.conjOperator_apply]
  have hinv :
      (allSiteT (Index := OddRow q)).toLinearEquiv.symm
          (toQubitOperator (cssZCheck logical)
            ((allSiteT (Index := OddRow q))
              (BinaryRowFamily.logicalPlusState (OddRow q)))) =
        toQubitOperator (cssZCheck logical)
          (BinaryRowFamily.logicalPlusState (OddRow q)) := by
    apply (allSiteT (Index := OddRow q)).toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (allSiteT_commutes_logicalZ logical
      (BinaryRowFamily.logicalPlusState (OddRow q))).symm
  rw [hinv]
  have hrelation := LinearMap.congr_fun
    (localX_logicalZ_relation a logical)
    (BinaryRowFamily.logicalPlusState (OddRow q))
  simp only [Module.End.mul_apply] at hrelation
  by_cases hbit : logical a = 0
  · simp only [if_pos hbit] at hrelation ⊢
    rw [hrelation, Module.End.mul_apply, localX_logicalPlusState]
    exact allSiteT_commutes_logicalZ logical
      (BinaryRowFamily.logicalPlusState (OddRow q))
  · simp only [if_neg hbit] at hrelation ⊢
    rw [hrelation, LinearMap.neg_apply, Module.End.mul_apply, map_neg,
      localX_logicalPlusState,
      allSiteT_commutes_logicalZ]
@[simp] theorem logicalABasisProjector_negative_logicalErrorState {q : Nat}
    (a : OddRow q) (logical : Word (ZMod 2) (OddRow q)) :
    logicalABasisProjector a .negative (logicalErrorState logical) =
      if logical a = 0 then 0 else logicalErrorState logical := by
  by_cases hbit : logical a = 0
  · rw [if_pos hbit]
    simp only [logicalABasisProjector, StabilizerOutcome.sign,
      LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
    rw [logicalABasisObservable_logicalErrorState, if_pos hbit]
    module
  · rw [if_neg hbit]
    simp only [logicalABasisProjector, StabilizerOutcome.sign,
      LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
    rw [logicalABasisObservable_logicalErrorState, if_neg hbit]
    module
noncomputable def logicalErrorDensity {q : Nat}
    (logical : Word (ZMod 2) (OddRow q)) :
    DensityOperator (LogicalRegister q) :=
  DensityOperator.pureDensity (logicalErrorState logical)
    (logicalErrorState_normSq logical)
@[simp] theorem logicalErrorDensity_toOperator {q : Nat}
    (logical : Word (ZMod 2) (OddRow q)) :
    (logicalErrorDensity logical).toOperator =
      (InnerProductSpace.rankOne Complex
        (logicalErrorState logical) (logicalErrorState logical)).toLinearMap := by
  rw [logicalErrorDensity, DensityOperator.pureDensity_toOperator]
noncomputable def logicalABasisBranchLinearMap {q : Nat}
    (a : OddRow q) (outcome : StabilizerOutcome) :
    Operator (LogicalRegister q) →ₗ[Complex] Operator (LogicalRegister q) where
  toFun := (logicalABasisInstrument a).branchOperator outcome
  map_add' := by
    intro A B
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _hindex
    by_cases hobserve : (logicalABasisInstrument a).observe index = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply, map_add]
    · simp [hobserve]
  map_smul' := by
    intro scalar A
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _hindex
    by_cases hobserve : (logicalABasisInstrument a).observe index = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]
noncomputable def logicalABasisNegativeWeight {q : Nat} (a : OddRow q)
    (rho : DensityOperator (LogicalRegister q)) : ℝ :=
  (logicalABasisInstrument a).bornWeight .negative rho
noncomputable def bh12ABasisOutputError {q : Nat} (a : OddRow q)
    (rho sigma : DensityOperator (LogicalRegister q)) : ℝ :=
  |logicalABasisNegativeWeight a rho - logicalABasisNegativeWeight a sigma|
theorem bh12ABasisOutputError_nonneg {q : Nat} (a : OddRow q)
    (rho sigma : DensityOperator (LogicalRegister q)) :
    0 ≤ bh12ABasisOutputError a rho sigma :=
  abs_nonneg _
noncomputable def bh12MagicStateDistillationProtocol (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (_hsuccess : 0 < rawSuccessMass q p) :
    MagicStateDistillationProtocol Qubit.QubitSpace
      (PhysicalRegister q) (LogicalRegister q) where
  run := resourceDecodedRun q (noisyResources q p)
  inputErrorModel := .independent (bh12IndependentInputModel q p)
  inputPermitted := bh12IndependentInputModel_permits q p
  behavior := .postselected
  idealOutput := bh12IdealOutput q
  outputError := bh12ABasisOutputError a
  outputError_nonneg := bh12ABasisOutputError_nonneg a
end BH12Protocol
end Triorthogonal
end Distillation
end QEC


