-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
-- name    : QEC_Distillation_Triorthogonal_Concatenation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T22:22:12.80101+00:00
-- url     : https://prove2.me/theorems/6baf02c3-c40a-476b-b078-2a8cead23cc3
-- title:
--   Concatenation
-- statement:
--   Definitions and structural lemmas for Concatenation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_apply
import Theorems.Thm_QEC_Distillation_DependentBatch_transposeRouting_childInputSlot
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aOneDensity_rankOne
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aZeroDensity_rankOne
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12MagicStateDistillationProtocol_quadratic
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decodedMarginalError_le_evenFamily_quadratic
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decodedMarginalError_nonneg
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawLogicalErrorWeight_nonneg
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_successProbability_noisyResources
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_sum_rawLogicalErrorWeight
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
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_apply
attribute [local simp] QEC.Distillation.DependentBatch.transposeRouting_childInputSlot
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
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
def bh12InputCount (q : Nat) : Nat :=
  resourceCount q
def bh12OutputCount (q : Nat) : Nat :=
  logicalCount q
noncomputable def bh12BlockRatio (q : Nat) : ℝ :=
  (bh12InputCount q : ℝ) / bh12OutputCount q
noncomputable def bh12BlockExponent (q : Nat) : ℝ :=
  Real.log (bh12BlockRatio q) / Real.log 2
def quadraticCoefficient (q : Nat) : ℝ :=
  8 * ((1 + 6 * q : Nat) : ℝ)
theorem quadraticCoefficient_pos (q : Nat) : 0 < quadraticCoefficient q := by
  unfold quadraticCoefficient
  positivity
abbrev depthTwoRawInputSlots (q : Nat) :=
  Fin (bh12InputCount q) × Fin (bh12InputCount q)
abbrev depthTwoParentOutputSlots (q : Nat) :=
  Fin (bh12InputCount q) × Fin (bh12OutputCount q)
abbrev depthTwoChildInputSlots (q : Nat) :=
  Fin (bh12OutputCount q) × Fin (bh12InputCount q)
abbrev depthTwoPotentialOutputSlots (q : Nat) :=
  Fin (bh12OutputCount q) × Fin (bh12OutputCount q)
def depthTwoRouting (q : Nat) :
    depthTwoParentOutputSlots q ≃ depthTwoChildInputSlots q :=
  DependentBatch.transposeRouting (bh12InputCount q) (bh12OutputCount q)
@[simp] theorem depthTwoRouting_apply (q : Nat)
    (parent : Fin (bh12InputCount q)) (port : Fin (bh12OutputCount q)) :
    depthTwoRouting q (parent, port) = (port, parent) :=
  rfl
noncomputable def bh12ActualRun (q : Nat) (p : ErrorParameter) :
    DistillationRun Qubit.QubitSpace (PhysicalRegister q) (LogicalRegister q) :=
  resourceDecodedRun q (noisyResources q p)
theorem bh12ActualRun_successProbability (q : Nat) (p : ErrorParameter) :
    (bh12ActualRun q p).successProbability = rawSuccessMass q p := by
  simpa [bh12ActualRun] using
    resourceDecodedRun_successProbability_noisyResources q p
theorem bh12AllZeroAccepted (q : Nat) :
    Accepts (0 : PhysicalError q) := by
  rw [accepts_iff_pairing_even_rows]
  intro check
  simp
theorem bh12AllZeroWordProbability (q : Nat) (p : ErrorParameter) :
    errorWordProbability p (0 : PhysicalError q) =
      (1 - p.rate) ^ bh12InputCount q := by
  simp [errorWordProbability, ErrorParameter.cleanWeight,
    bh12InputCount, resourceCount]
theorem rawSuccessMass_allZeroWord_le (q : Nat) (p : ErrorParameter) :
    (1 - p.rate) ^ bh12InputCount q ≤ rawSuccessMass q p := by
  classical
  rw [rawSuccessMass]
  calc
    (1 - p.rate) ^ bh12InputCount q =
        if Accepts (0 : PhysicalError q) then
          errorWordProbability p (0 : PhysicalError q) else 0 := by
      rw [if_pos (bh12AllZeroAccepted q)]
      exact (bh12AllZeroWordProbability q p).symm
    _ ≤ ∑ error : PhysicalError q,
        if Accepts error then errorWordProbability p error else 0 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun error : PhysicalError q =>
          if Accepts error then errorWordProbability p error else 0)
        (fun error _ => by
          by_cases haccept : Accepts error
          · simp [haccept, errorWordProbability_nonneg p error]
          · simp [haccept])
        (Finset.mem_univ _)
theorem rawSuccessMass_one_sub_inputCount_rate_le (q : Nat) (p : ErrorParameter) :
    1 - (bh12InputCount q : ℝ) * p.rate ≤ rawSuccessMass q p := by
  calc
    1 - (bh12InputCount q : ℝ) * p.rate =
        1 + (bh12InputCount q : ℝ) * ((1 - p.rate) - 1) := by ring
    _ ≤ (1 - p.rate) ^ bh12InputCount q := by
      simpa using one_add_mul_sub_le_pow
        (a := 1 - p.rate) (by linarith [p.rate_le_one]) (bh12InputCount q)
    _ ≤ rawSuccessMass q p := rawSuccessMass_allZeroWord_le q p
theorem bh12ActualRun_successProbability_one_sub_inputCount_rate_le
    (q : Nat) (p : ErrorParameter) :
    1 - (bh12InputCount q : ℝ) * p.rate ≤
      (bh12ActualRun q p).successProbability := by
  rw [bh12ActualRun_successProbability]
  exact rawSuccessMass_one_sub_inputCount_rate_le q p
theorem bh12ActualRun_three_quarters_le_successProbability (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    (3 : ℝ) / 4 ≤ (bh12ActualRun q p).successProbability := by
  calc
    (3 : ℝ) / 4 ≤ 1 - (bh12InputCount q : ℝ) * p.rate := by linarith
    _ ≤ (bh12ActualRun q p).successProbability :=
      bh12ActualRun_successProbability_one_sub_inputCount_rate_le q p
theorem bh12ActualRun_successProbability_pos_of_small_error (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4) :
    0 < (bh12ActualRun q p).successProbability := by
  exact lt_of_lt_of_le (by norm_num)
    (bh12ActualRun_three_quarters_le_successProbability q p hsmall)
noncomputable def bh12AcceptedOutput (q : Nat) (p : ErrorParameter) :
    DensityOperator (LogicalRegister q) :=
  (bh12ActualRun q p).acceptedOutput
noncomputable def bh12SelectedPortSubsystem (q : Nat) (port : OddRow q) :
    FiniteSubsystem (OddRow q) :=
  ⟨{port}⟩
noncomputable def bh12SelectedPortCoordinate (q : Nat) (port : OddRow q) :
    (bh12SelectedPortSubsystem q port).SelectedCoordinates :=
  ⟨port, by simp [bh12SelectedPortSubsystem]⟩
theorem bh12SelectedPortCoordinate_eq (q : Nat) (port : OddRow q)
    (coordinate : (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    coordinate = bh12SelectedPortCoordinate q port := by
  apply Subtype.ext
  have hmem : (coordinate : OddRow q) ∈ ({port} : Finset (OddRow q)) :=
    coordinate.property
  exact Finset.mem_singleton.mp hmem
def bh12SelectedPortBitstringEquiv (q : Nat) (port : OddRow q) :
    Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates ≃ Fin 2 where
  toFun := fun bits => bits (bh12SelectedPortCoordinate q port)
  invFun := fun bit _ => bit
  left_inv := by
    intro bits
    funext coordinate
    rw [bh12SelectedPortCoordinate_eq q port coordinate]
  right_inv := by
    intro bit
    rfl
noncomputable def bh12SelectedPortTransport (q : Nat) (port : OddRow q) :
    UnitaryTransport (bh12SelectedPortSubsystem q port).selectedSystem
      Qubit.QubitSpace := by
  let sourceBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis (bh12SelectedPortBitstringEquiv q port)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp] theorem bh12SelectedPortTransport_apply_basis (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    bh12SelectedPortTransport q port
      (EuclideanSpace.basisFun _ Complex bits) =
      EuclideanSpace.basisFun _ Complex
        (bh12SelectedPortBitstringEquiv q port bits) := by
  dsimp [bh12SelectedPortTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
def bh12SelectedPortAnchorBitstring (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Qubit.Bitstring (OddRow q) :=
  (bh12SelectedPortSubsystem q port).recombineBitstring ((fun _ => 0), bits)
noncomputable def bh12SelectedPortComplementErrorState (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    (bh12SelectedPortSubsystem q port).complementSystem :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex) * logicalErrorState logical
      (bh12SelectedPortAnchorBitstring q port bits)
@[simp] theorem bh12SelectedPortComplementErrorState_apply
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    bh12SelectedPortComplementErrorState q port logical bits =
      (Real.sqrt 2 : Complex) * logicalErrorState logical
        (bh12SelectedPortAnchorBitstring q port bits) :=
  rfl
theorem bh12LogicalErrorState_apply (q : Nat)
    (logical : Coding.Word (ZMod 2) (OddRow q))
    (bits : Qubit.Bitstring (OddRow q)) :
    logicalErrorState logical bits =
      Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical) bits *
        (BinaryRowFamily.logicalUniformScalar (OddRow q) *
          BinaryRowFamily.piDivFourPhase ^
            Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv
              (OddRow q) bits)) := by
  simp [logicalErrorState, Coding.PauliSymplectic.toQubitOperator_apply,
    Coding.PauliSymplectic.cssZCheck, Coding.PauliSymplectic.xSupport,
    Coding.PauliSymplectic.zSupport]
theorem bh12SelectedPortAnchorBitstring_apply_port (q : Nat) (port : OddRow q)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    bh12SelectedPortAnchorBitstring q port bits port = 0 := by
  simp [bh12SelectedPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    bh12SelectedPortSubsystem]
theorem bh12SelectedPortRecombineBitstring_apply_port (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) port =
      left (bh12SelectedPortCoordinate q port) := by
  simp only [FiniteSubsystem.recombineBitstring]
  rw [dif_pos (by simp [bh12SelectedPortSubsystem])]
  let coordinate : (bh12SelectedPortSubsystem q port).SelectedCoordinates :=
    ⟨port, by simp [bh12SelectedPortSubsystem]⟩
  change left coordinate = left (bh12SelectedPortCoordinate q port)
  rw [bh12SelectedPortCoordinate_eq q port coordinate]
theorem bh12SelectedPortRecombineBitstring_apply_ne (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates)
    (site : OddRow q) (hsite : site ≠ port) :
    (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) site =
      bh12SelectedPortAnchorBitstring q port right site := by
  simp [bh12SelectedPortAnchorBitstring, FiniteSubsystem.recombineBitstring,
    bh12SelectedPortSubsystem, hsite]
theorem bh12SelectedPortHammingWeight_recombine (q : Nat) (port : OddRow q)
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
      ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right))) =
      (bh12SelectedPortBitstringEquiv q port left).val +
        Coding.HammingWeight (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          (bh12SelectedPortAnchorBitstring q port right)) := by
  classical
  generalize hbit : bh12SelectedPortBitstringEquiv q port left = bit
  fin_cases bit
  · have hleft : left (bh12SelectedPortCoordinate q port) = 0 := by
      simpa [bh12SelectedPortBitstringEquiv] using hbit
    have heq :
        (bh12SelectedPortSubsystem q port).recombineBitstring (left, right) =
          bh12SelectedPortAnchorBitstring q port right := by
      funext site
      by_cases hsite : site = port
      · subst site
        rw [bh12SelectedPortRecombineBitstring_apply_port,
          bh12SelectedPortAnchorBitstring_apply_port, hleft]
      · exact bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite
    simp [heq]
  · have hleft : left (bh12SelectedPortCoordinate q port) = 1 := by
      simpa [bh12SelectedPortBitstringEquiv] using hbit
    have hsupp :
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right))) =
          insert port
            (Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
              (bh12SelectedPortAnchorBitstring q port right))) := by
      ext site
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and,
        Coding.PauliSymplectic.bitstringWordEquiv_apply]
      by_cases hsite : site = port
      · subst site
        norm_num [
          bh12SelectedPortRecombineBitstring_apply_port,
          bh12SelectedPortAnchorBitstring_apply_port, hleft]
        exact (one_ne_zero : (1 : ZMod 2) ≠ 0)
      · have happly :=
          bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite
        simp only [happly, hsite, false_or]
    have hnotmem : port ∉
        Coding.hammingSupport (Coding.PauliSymplectic.bitstringWordEquiv (OddRow q)
          (bh12SelectedPortAnchorBitstring q port right)) := by
      simp only [Coding.hammingSupport]
      erw [Finset.mem_filter]
      simp [Coding.PauliSymplectic.bitstringWordEquiv_apply,
        bh12SelectedPortAnchorBitstring_apply_port]
      rfl
    simp only [Coding.HammingWeight, hsupp,
      Finset.card_insert_of_notMem hnotmem]
    omega
theorem bh12SelectedPortZSupportPhase_recombine (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q))
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical)
      ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
      (if logical port = 0 then 1 else
        Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left)) *
        Qubit.zSupportPhase (Coding.PauliSymplectic.binarySupport logical)
          (bh12SelectedPortAnchorBitstring q port right) := by
  classical
  let support := Coding.PauliSymplectic.binarySupport logical
  by_cases hmem : port ∈ support
  · have hlogical : logical port ≠ 0 := by
      simpa [support, Coding.PauliSymplectic.binarySupport] using hmem
    have hprod :
        Qubit.zSupportPhase (support.erase port)
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zSupportPhase (support.erase port)
            (bh12SelectedPortAnchorBitstring q port right) := by
      unfold Qubit.zSupportPhase
      apply Finset.prod_congr rfl
      intro site hsite
      have hsite_ne : site ≠ port := Finset.ne_of_mem_erase hsite
      rw [bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite_ne]
    calc
      Qubit.zSupportPhase support
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zPhase
              ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right) port) *
            Qubit.zSupportPhase (support.erase port)
              ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) := by
            unfold Qubit.zSupportPhase
            nth_rewrite 1 [← Finset.insert_erase hmem]
            rw [Finset.prod_insert (Finset.notMem_erase _ _)]
      _ = Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left) *
            Qubit.zSupportPhase (support.erase port)
              (bh12SelectedPortAnchorBitstring q port right) := by
            rw [bh12SelectedPortRecombineBitstring_apply_port, hprod]
            rfl
      _ = (if logical port = 0 then 1 else
            Qubit.zPhase (bh12SelectedPortBitstringEquiv q port left)) *
          Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) := by
            have hanchor :
                Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) =
                  Qubit.zSupportPhase (support.erase port)
                    (bh12SelectedPortAnchorBitstring q port right) := by
              unfold Qubit.zSupportPhase
              calc
                (∏ i ∈ support, Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i)) =
                    ∏ i ∈ insert port (support.erase port),
                      Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      nth_rewrite 1 [← Finset.insert_erase hmem]
                      rfl
                _ = Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right port) *
                    ∏ i ∈ support.erase port,
                      Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      rw [Finset.prod_insert (Finset.notMem_erase _ _)]
                _ = ∏ i ∈ support.erase port,
                    Qubit.zPhase (bh12SelectedPortAnchorBitstring q port right i) := by
                      rw [bh12SelectedPortAnchorBitstring_apply_port]
                      simp
            rw [if_neg hlogical]
            rw [hanchor]
  · have hlogical : logical port = 0 := by
      by_contra hlogical
      apply hmem
      simp [support, Coding.PauliSymplectic.binarySupport, hlogical]
    have hprod :
        Qubit.zSupportPhase support
          ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
          Qubit.zSupportPhase support (bh12SelectedPortAnchorBitstring q port right) := by
      unfold Qubit.zSupportPhase
      apply Finset.prod_congr rfl
      intro site hsite
      have hsite_ne : site ≠ port := by
        intro hsite_eq
        subst site
        exact hmem hsite
      rw [bh12SelectedPortRecombineBitstring_apply_ne q port left right site hsite_ne]
    rw [hprod, if_pos hlogical, one_mul]
theorem bh12SelectedPortLogicalErrorState_recombine_amplitude
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (left : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates)
    (right : Qubit.Bitstring (bh12SelectedPortSubsystem q port).ComplementCoordinates) :
    logicalErrorState logical
        ((bh12SelectedPortSubsystem q port).recombineBitstring (left, right)) =
      (if logical port = 0 then OneQubit.aZeroState else OneQubit.aOneState)
          (bh12SelectedPortBitstringEquiv q port left) *
        bh12SelectedPortComplementErrorState q port logical right := by
  rw [bh12LogicalErrorState_apply, bh12SelectedPortComplementErrorState_apply,
    bh12LogicalErrorState_apply, bh12SelectedPortHammingWeight_recombine,
    bh12SelectedPortZSupportPhase_recombine]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  generalize hbit : bh12SelectedPortBitstringEquiv q port left = bit
  fin_cases bit <;> by_cases hlogical : logical port = 0
  all_goals simp [hlogical, OneQubit.aZeroState, OneQubit.aOneState,
    OneQubit.zTransport, OneQubit.zLinearEquiv, OneQubitMagic.phaseState,
    Qubit.pauliZ_apply, BinaryRowFamily.piDivFourPhase]
  all_goals field_simp [hsqrt_ne]
  all_goals ring
theorem bh12SelectedPortTransport_symm_apply (q : Nat) (port : OddRow q)
    (psi : Qubit.QubitSpace)
    (bits : Qubit.Bitstring (bh12SelectedPortSubsystem q port).SelectedCoordinates) :
    (bh12SelectedPortTransport q port).symm psi bits =
      psi (bh12SelectedPortBitstringEquiv q port bits) := by
  have hinner := (bh12SelectedPortTransport q port).map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((bh12SelectedPortTransport q port).symm psi)
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [bh12SelectedPortTransport_apply_basis, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
theorem bh12SelectedPortRegisterFactorization_symm_tmul_apply
    (q : Nat) (port : OddRow q)
    (leftState : (bh12SelectedPortSubsystem q port).selectedSystem)
    (rightState : (bh12SelectedPortSubsystem q port).complementSystem)
    (bits : Qubit.Bitstring (OddRow q)) :
    (bh12SelectedPortSubsystem q port).registerFactorization.symm
        (leftState ⊗ₜ[Complex] rightState) bits =
      leftState ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        rightState ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
  have hinner := (bh12SelectedPortSubsystem q port).registerFactorization.map_inner
    (EuclideanSpace.basisFun _ Complex bits)
    ((bh12SelectedPortSubsystem q port).registerFactorization.symm
      (leftState ⊗ₜ[Complex] rightState))
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply] at hinner
  rw [FiniteSubsystem.registerFactorization_apply_basis, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner.symm
theorem bh12SelectedPortLogicalErrorState_factorization (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    (bh12SelectedPortSubsystem q port).registerFactorization
        (logicalErrorState logical) =
      (if logical port = 0 then
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
      else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex]
        bh12SelectedPortComplementErrorState q port logical := by
  apply (bh12SelectedPortSubsystem q port).registerFactorization.symm.toLinearEquiv.injective
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_apply_apply]
  ext bits
  change logicalErrorState logical bits =
    (bh12SelectedPortSubsystem q port).registerFactorization.symm
      ((if logical port = 0 then
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
      else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex]
        bh12SelectedPortComplementErrorState q port logical) bits
  rw [bh12SelectedPortRegisterFactorization_symm_tmul_apply]
  have hsplit :
      (bh12SelectedPortSubsystem q port).recombineBitstring
          ((bh12SelectedPortSubsystem q port).splitBitstring bits) = bits := by
    simpa [FiniteSubsystem.bitstringFactorization] using
      (bh12SelectedPortSubsystem q port).bitstringFactorization.symm_apply_apply bits
  by_cases hlogical : logical port = 0
  · rw [if_pos hlogical]
    change logicalErrorState logical bits =
      (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
        ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        bh12SelectedPortComplementErrorState q port logical
          ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
    rw [bh12SelectedPortTransport_symm_apply]
    calc
      logicalErrorState logical bits =
          logicalErrorState logical
            ((bh12SelectedPortSubsystem q port).recombineBitstring
              ((bh12SelectedPortSubsystem q port).splitBitstring bits)) := by rw [hsplit]
      _ = OneQubit.aZeroState
            (bh12SelectedPortBitstringEquiv q port
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).1) *
            bh12SelectedPortComplementErrorState q port logical
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
            simpa [hlogical] using
              bh12SelectedPortLogicalErrorState_recombine_amplitude q port logical
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).1
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
  · rw [if_neg hlogical]
    change logicalErrorState logical bits =
      (bh12SelectedPortTransport q port).symm OneQubit.aOneState
        ((bh12SelectedPortSubsystem q port).splitBitstring bits).1 *
        bh12SelectedPortComplementErrorState q port logical
          ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
    rw [bh12SelectedPortTransport_symm_apply]
    calc
      logicalErrorState logical bits =
          logicalErrorState logical
            ((bh12SelectedPortSubsystem q port).recombineBitstring
              ((bh12SelectedPortSubsystem q port).splitBitstring bits)) := by rw [hsplit]
      _ = OneQubit.aOneState
            (bh12SelectedPortBitstringEquiv q port
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).1) *
            bh12SelectedPortComplementErrorState q port logical
              ((bh12SelectedPortSubsystem q port).splitBitstring bits).2 := by
            simpa [hlogical] using
              bh12SelectedPortLogicalErrorState_recombine_amplitude q port logical
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).1
                ((bh12SelectedPortSubsystem q port).splitBitstring bits).2
theorem bh12SelectedPortComplementErrorState_inner_self (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) :
    inner Complex (bh12SelectedPortComplementErrorState q port logical)
      (bh12SelectedPortComplementErrorState q port logical) = 1 := by
  have hglobal : inner Complex (logicalErrorState logical) (logicalErrorState logical) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hnorm : ‖logicalErrorState logical‖ = 1 := by
      nlinarith [norm_nonneg (logicalErrorState logical), logicalErrorState_normSq logical]
    rw [hnorm]
    norm_num
  have hlocal :
      inner Complex
          (if logical port = 0 then
            (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
          else (bh12SelectedPortTransport q port).symm OneQubit.aOneState)
          (if logical port = 0 then
            (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
          else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) = 1 := by
    by_cases hlogical : logical port = 0
    · rw [if_pos hlogical]
      calc
        inner Complex ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState)
            ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState) =
            inner Complex
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState))
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aZeroState)) :=
              ((bh12SelectedPortTransport q port).map_inner _ _).symm
        _ = inner Complex OneQubit.aZeroState OneQubit.aZeroState := by
              simp only [UnitaryTransport.symm_toLinearEquiv,
                LinearEquiv.apply_symm_apply]
        _ = 1 := by
              rw [inner_self_eq_norm_sq_to_K]
              simp
    · rw [if_neg hlogical]
      calc
        inner Complex ((bh12SelectedPortTransport q port).symm OneQubit.aOneState)
            ((bh12SelectedPortTransport q port).symm OneQubit.aOneState) =
            inner Complex
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aOneState))
              ((bh12SelectedPortTransport q port)
                ((bh12SelectedPortTransport q port).symm OneQubit.aOneState)) :=
              ((bh12SelectedPortTransport q port).map_inner _ _).symm
        _ = inner Complex OneQubit.aOneState OneQubit.aOneState := by
              simp only [UnitaryTransport.symm_toLinearEquiv,
                LinearEquiv.apply_symm_apply]
        _ = 1 := by
              rw [OneQubit.aOneState_eq_pauliZ, OneQubit.pauliZ_map_inner,
                inner_self_eq_norm_sq_to_K]
              simp
  have hfactorNorm :
      inner Complex
          ((bh12SelectedPortSubsystem q port).registerFactorization
            (logicalErrorState logical))
          ((bh12SelectedPortSubsystem q port).registerFactorization
            (logicalErrorState logical)) = 1 := by
    rw [(bh12SelectedPortSubsystem q port).registerFactorization.map_inner]
    exact hglobal
  rw [bh12SelectedPortLogicalErrorState_factorization, TensorProduct.inner_tmul,
    hlocal, one_mul] at hfactorNorm
  exact hfactorNorm
theorem bh12SelectedPortTransport_partialTrace_pure_aZero_of_factorized
    (q : Nat) (port : OddRow q) (psi : LogicalRegister q)
    (hpsi : ‖psi‖ ^ 2 = 1)
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization psi =
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    (bh12SelectedPortTransport q port).conjDensity
      ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (DensityOperator.pureDensity psi hpsi)) = OneQubit.aZeroDensity := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactor]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [hrest]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact OneQubit.aZeroDensity_rankOne.symm
theorem bh12SelectedPortTransport_partialTrace_pure_aOne_of_factorized
    (q : Nat) (port : OddRow q) (psi : LogicalRegister q)
    (hpsi : ‖psi‖ ^ 2 = 1)
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization psi =
        (bh12SelectedPortTransport q port).symm OneQubit.aOneState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    (bh12SelectedPortTransport q port).conjDensity
      ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
        (DensityOperator.pureDensity psi hpsi)) = OneQubit.aOneDensity := by
  apply DensityOperator.ext_toOperator
  simp only [UnitaryTransport.conjDensity_toOperator,
    QuantumChannel.mapDensity_toOperator,
    FiniteSubsystem.selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
    QuantumChannel.unitaryConj_apply, FiniteSubsystem.selectedPartialTrace,
    DensityOperator.pureDensity_toOperator]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactor]
  rw [partialTraceRightRaw_cptp_toLinearMap]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [hrest]
  simp only [one_smul]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact OneQubit.aOneDensity_rankOne.symm
noncomputable def bh12SelectedPortDensity (q : Nat) (p : ErrorParameter)
    (port : OddRow q) :
    DensityOperator (bh12SelectedPortSubsystem q port).selectedSystem :=
  (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
    (bh12AcceptedOutput q p)
theorem bh12RawMarginalErrorWeight_le_rawSuccessMass (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawMarginalErrorWeight q p port ≤ rawSuccessMass q p := by
  calc
    rawMarginalErrorWeight q p port =
        ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          if logical port = 0 then 0 else rawLogicalErrorWeight q p logical := rfl
    _ ≤ ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          rawLogicalErrorWeight q p logical := by
      apply Finset.sum_le_sum
      intro logical _
      by_cases hbit : logical port = 0
      · simp [hbit, rawLogicalErrorWeight_nonneg]
      · simp [hbit]
    _ = rawSuccessMass q p := sum_rawLogicalErrorWeight q p
theorem bh12DecodedMarginalError_le_one (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    decodedMarginalError q p hsuccess port ≤ 1 := by
  simp only [decodedMarginalError, dif_pos hsuccess]
  rw [div_le_one₀ hsuccess]
  exact bh12RawMarginalErrorWeight_le_rawSuccessMass q p port
noncomputable def bh12DecodedMarginalErrorParameter (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) : ErrorParameter where
  rate := decodedMarginalError q p hsuccess port
  rate_nonneg := decodedMarginalError_nonneg q p hsuccess port
  rate_le_one := bh12DecodedMarginalError_le_one q p hsuccess port
@[simp] theorem bh12DecodedMarginalErrorParameter_rate (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    (bh12DecodedMarginalErrorParameter q p hsuccess port).rate =
      decodedMarginalError q p hsuccess port :=
  rfl
noncomputable def bh12SelectedPortTransportedDensity (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    (bh12SelectedPortDensity q p port)
noncomputable def bh12SelectedPortLogicalErrorDensity (q : Nat) (port : OddRow q)
    (logical : Coding.Word (ZMod 2) (OddRow q)) : DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (logicalErrorDensity logical))
theorem bh12SelectedPortLogicalErrorDensity_eq_aZeroDensity_of_factorized
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (bh12SelectedPortTransport q port).symm OneQubit.aZeroState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical = OneQubit.aZeroDensity := by
  simpa [bh12SelectedPortLogicalErrorDensity, logicalErrorDensity] using
    bh12SelectedPortTransport_partialTrace_pure_aZero_of_factorized q port
      (logicalErrorState logical) (logicalErrorState_normSq logical) rest hfactor hrest
theorem bh12SelectedPortLogicalErrorDensity_eq_aOneDensity_of_factorized
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (bh12SelectedPortTransport q port).symm OneQubit.aOneState ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical = OneQubit.aOneDensity := by
  simpa [bh12SelectedPortLogicalErrorDensity, logicalErrorDensity] using
    bh12SelectedPortTransport_partialTrace_pure_aOne_of_factorized q port
      (logicalErrorState logical) (logicalErrorState_normSq logical) rest hfactor hrest
theorem bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_of_factorization
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q))
    (rest : (bh12SelectedPortSubsystem q port).complementSystem)
    (hfactor :
      (bh12SelectedPortSubsystem q port).registerFactorization
          (logicalErrorState logical) =
        (if logical port = 0 then
          (bh12SelectedPortTransport q port).symm OneQubit.aZeroState
        else (bh12SelectedPortTransport q port).symm OneQubit.aOneState) ⊗ₜ[Complex] rest)
    (hrest : inner Complex rest rest = 1) :
    bh12SelectedPortLogicalErrorDensity q port logical =
      if logical port = 0 then OneQubit.aZeroDensity else OneQubit.aOneDensity := by
  by_cases hbit : logical port = 0
  · rw [if_pos hbit] at hfactor ⊢
    exact bh12SelectedPortLogicalErrorDensity_eq_aZeroDensity_of_factorized
      q port logical rest hfactor hrest
  · rw [if_neg hbit] at hfactor ⊢
    exact bh12SelectedPortLogicalErrorDensity_eq_aOneDensity_of_factorized
      q port logical rest hfactor hrest
theorem bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_actual
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q)) :
    bh12SelectedPortLogicalErrorDensity q port logical =
      if logical port = 0 then OneQubit.aZeroDensity else OneQubit.aOneDensity := by
  exact bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_of_factorization
    q port logical (bh12SelectedPortComplementErrorState q port logical)
    (bh12SelectedPortLogicalErrorState_factorization q port logical)
    (bh12SelectedPortComplementErrorState_inner_self q port logical)
noncomputable def bh12SelectedPortTransportedChannel (q : Nat)
    (port : OddRow q) :
    QuantumChannel (LogicalRegister q) Qubit.QubitSpace :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj (bh12SelectedPortTransport q port))
    (bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister
theorem bh12SelectedPortTransportedDensity_toOperator (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (bh12SelectedPortTransportedDensity q p port).toOperator =
      bh12SelectedPortTransportedChannel q port
        (bh12AcceptedOutput q p).toOperator :=
  rfl
theorem bh12SelectedPortTransportedChannel_logicalErrorDensity
    (q : Nat) (port : OddRow q) (logical : Coding.Word (ZMod 2) (OddRow q)) :
    bh12SelectedPortTransportedChannel q port
        (logicalErrorDensity logical).toOperator =
      if logical port = 0 then OneQubit.aZeroDensity.toOperator
      else OneQubit.aOneDensity.toOperator := by
  change (bh12SelectedPortLogicalErrorDensity q port logical).toOperator = _
  simpa only [apply_ite] using congrArg DensityOperator.toOperator
    (bh12SelectedPortLogicalErrorDensity_eq_aBasisBranch_actual q port logical)
theorem bh12RawMarginalErrorWeight_eq_errorWordSum (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawMarginalErrorWeight q p port =
      ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          errorWordProbability p error else 0 := by
  classical
  unfold rawMarginalErrorWeight rawLogicalErrorWeight
  calc
    (∑ logical : Coding.Word (ZMod 2) (OddRow q),
      if logical port = 0 then 0 else
        ∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error = logical then
            errorWordProbability p error else 0) =
        ∑ logical : Coding.Word (ZMod 2) (OddRow q),
          ∑ error : PhysicalError q,
            if logical port = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro logical _
      by_cases hlogical : logical port = 0 <;> simp [hlogical]
    _ = ∑ error : PhysicalError q,
          ∑ logical : Coding.Word (ZMod 2) (OddRow q),
            if logical port = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases haccept : Accepts error
      · by_cases hbit : logicalErrorWord error port = 0
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
      · simp [haccept]
theorem bh12RawSuccessMass_eq_zeroPlusMarginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    rawSuccessMass q p =
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          errorWordProbability p error else 0) +
        rawMarginalErrorWeight q p port := by
  rw [bh12RawMarginalErrorWeight_eq_errorWordSum]
  change (∑ error : PhysicalError q,
    if Accepts error then errorWordProbability p error else 0) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro error _
  by_cases haccept : Accepts error
  · by_cases hbit : logicalErrorWord error port = 0 <;>
      simp [haccept, hbit]
  · simp [haccept]
theorem bh12RawZeroBitWeight_eq_success_sub_marginal (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (∑ error : PhysicalError q,
      if Accepts error ∧ logicalErrorWord error port = 0 then
        errorWordProbability p error else 0) =
      rawSuccessMass q p - rawMarginalErrorWeight q p port := by
  linarith [bh12RawSuccessMass_eq_zeroPlusMarginal q p port]
theorem bh12SelectedPortTransported_errorWordSum_grouped (q : Nat)
    (p : ErrorParameter) (port : OddRow q) :
    (∑ error : PhysicalError q,
      if Accepts error then
        (errorWordProbability p error : Complex) •
          (if logicalErrorWord error port = 0 then OneQubit.aZeroDensity.toOperator
          else OneQubit.aOneDensity.toOperator)
      else 0) =
      ((rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) •
        OneQubit.aZeroDensity.toOperator) +
      ((rawMarginalErrorWeight q p port : Complex) •
        OneQubit.aOneDensity.toOperator) := by
  have hzero :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          errorWordProbability p error else 0) =
        rawSuccessMass q p - rawMarginalErrorWeight q p port :=
    bh12RawZeroBitWeight_eq_success_sub_marginal q p port
  have hzeroComplex :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port = 0 then
          (errorWordProbability p error : Complex) else 0) =
        (rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) := by
    convert congrArg (fun x : ℝ => (x : Complex)) hzero using 1
    · push_cast
      apply Finset.sum_congr rfl
      intro error _
      split <;> rfl
    · norm_cast
  have hmarginalComplex :
      (∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error port ≠ 0 then
          (errorWordProbability p error : Complex) else 0) =
        (rawMarginalErrorWeight q p port : Complex) := by
    convert congrArg (fun x : ℝ => (x : Complex))
      (bh12RawMarginalErrorWeight_eq_errorWordSum q p port).symm using 1
    · push_cast
      apply Finset.sum_congr rfl
      intro error _
      split <;> rfl
  calc
    (∑ error : PhysicalError q,
      if Accepts error then
        (errorWordProbability p error : Complex) •
          (if logicalErrorWord error port = 0 then OneQubit.aZeroDensity.toOperator
          else OneQubit.aOneDensity.toOperator)
      else 0) =
        ∑ error : PhysicalError q,
          ((if Accepts error ∧ logicalErrorWord error port = 0 then
            (errorWordProbability p error : Complex) else 0) •
              OneQubit.aZeroDensity.toOperator +
            (if Accepts error ∧ logicalErrorWord error port ≠ 0 then
              (errorWordProbability p error : Complex) else 0) •
                OneQubit.aOneDensity.toOperator) := by
          apply Finset.sum_congr rfl
          intro error _
          by_cases haccept : Accepts error
          · by_cases hbit : logicalErrorWord error port = 0 <;>
              simp [haccept, hbit]
          · simp [haccept]
    _ = ((∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error port = 0 then
            (errorWordProbability p error : Complex) else 0) •
            OneQubit.aZeroDensity.toOperator) +
        ((∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error port ≠ 0 then
            (errorWordProbability p error : Complex) else 0) •
            OneQubit.aOneDensity.toOperator) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul]
    _ = _ := by rw [hzeroComplex, hmarginalComplex]
theorem bh12SelectedPortTransportedDensity_eq_diagonalAResource (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (port : OddRow q) :
    bh12SelectedPortTransportedDensity q p port =
      OneQubit.diagonalAResource
        (bh12DecodedMarginalErrorParameter q p hsuccess port) := by
  apply DensityOperator.ext_toOperator
  rw [bh12SelectedPortTransportedDensity_toOperator, bh12AcceptedOutput,
    bh12ActualRun, resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
      q p hsuccess]
  simp only [map_smul, map_sum, apply_ite, map_zero]
  simp_rw [bh12SelectedPortTransportedChannel_logicalErrorDensity]
  rw [bh12SelectedPortTransported_errorWordSum_grouped]
  rw [OneQubit.diagonalAResource_toOperator]
  simp only [bh12DecodedMarginalErrorParameter_rate, ErrorParameter.cleanWeight,
    decodedMarginalError, dif_pos hsuccess,
    RCLike.real_smul_eq_coe_smul (K := Complex), map_sub, map_mul, map_inv₀,
    div_eq_mul_inv]
  have hsuccessComplex : (rawSuccessMass q p : Complex) ≠ 0 := by
    exact_mod_cast hsuccess.ne'
  have hzeroCoeff :
      (rawSuccessMass q p : Complex)⁻¹ *
          (rawSuccessMass q p - rawMarginalErrorWeight q p port : Complex) =
        1 - (rawMarginalErrorWeight q p port : Complex) *
          (rawSuccessMass q p : Complex)⁻¹ := by
    field_simp [hsuccessComplex]
  rw [smul_add, smul_smul, smul_smul, hzeroCoeff]
  ring_nf
  simp only [Complex.coe_algebraMap, Complex.ofReal_one]
noncomputable def bh12SelectedPortABasisError (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ℝ :=
  bh12ABasisOutputError port (bh12AcceptedOutput q p) (bh12IdealOutput q)
noncomputable def bh12AcceptedPortError (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) : ℝ :=
  decodedMarginalError q p hsuccess port
theorem bh12AcceptedPortError_le_quadratic (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q)
    (hhalf : p.rate ≤ 1 / 2) :
    bh12AcceptedPortError q p hsuccess port ≤
      quadraticCoefficient q * p.rate ^ 2 := by
  simpa [bh12AcceptedPortError, quadraticCoefficient] using
    decodedMarginalError_le_evenFamily_quadratic q p port hhalf
theorem bh12OneStepPhysicalInvariant (q : Nat) (p : ErrorParameter)
    (port : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∃ hsuccess : 0 < rawSuccessMass q p,
      0 < (bh12ActualRun q p).successProbability ∧
        bh12SelectedPortTransportedDensity q p port =
          OneQubit.diagonalAResource
            (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
          quadraticCoefficient q * p.rate ^ 2 ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ p.rate ∧
        (bh12InputCount q : ℝ) *
            (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 / 4 ∧
        (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 / 2 ∧
        quadraticCoefficient q *
            (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ 1 := by
  have hactualSuccess : 0 < (bh12ActualRun q p).successProbability :=
    bh12ActualRun_successProbability_pos_of_small_error q p hsmall
  have hsuccess : 0 < rawSuccessMass q p := by
    rw [← bh12ActualRun_successProbability q p]
    exact hactualSuccess
  have hquadratic :
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
        quadraticCoefficient q * p.rate ^ 2 := by
    simpa only [bh12DecodedMarginalErrorParameter_rate, bh12AcceptedPortError] using
      bh12AcceptedPortError_le_quadratic q p hsuccess port hhalf
  have hnonincrease :
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤ p.rate := by
    calc
      (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
          quadraticCoefficient q * p.rate ^ 2 := hquadratic
      _ = (quadraticCoefficient q * p.rate) * p.rate := by ring
      _ ≤ 1 * p.rate :=
        mul_le_mul_of_nonneg_right hquadraticSmall p.rate_nonneg
      _ = p.rate := one_mul _
  refine ⟨hsuccess, hactualSuccess,
    bh12SelectedPortTransportedDensity_eq_diagonalAResource q p hsuccess port,
    hquadratic, hnonincrease, ?_, hnonincrease.trans hhalf, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hnonincrease (by positivity)).trans hsmall
  · exact (mul_le_mul_of_nonneg_left hnonincrease
      (le_of_lt (quadraticCoefficient_pos q))).trans hquadraticSmall
def depthTwoChildInputSlot (q : Nat) (child : Fin (bh12OutputCount q))
    (parent : Fin (bh12InputCount q)) :
    depthTwoChildInputSlots q :=
  depthTwoRouting q (DependentBatch.childInputSlot child parent)
@[simp] theorem depthTwoChildInputSlot_apply (q : Nat)
    (child : Fin (bh12OutputCount q)) (parent : Fin (bh12InputCount q)) :
    depthTwoChildInputSlot q child parent = (child, parent) :=
  rfl
noncomputable def depthTwoFreshParentRun (q : Nat) (p : ErrorParameter)
    (_parent : Fin (bh12InputCount q)) :=
  bh12ActualRun q p
noncomputable def depthTwoFreshParentPortDensity (q : Nat) (p : ErrorParameter)
    (parent : Fin (bh12InputCount q)) (port : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (depthTwoFreshParentRun q p parent).acceptedOutput)
noncomputable def depthTwoChildResources (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ResourceInput (bh12InputCount q) Qubit.QubitSpace :=
  fun parent => depthTwoFreshParentPortDensity q p parent port
noncomputable def depthTwoChildRun (q : Nat) (p : ErrorParameter)
    (port : OddRow q) :=
  resourceDecodedRun q (depthTwoChildResources q p port)
noncomputable def depthTwoChildSelectedPortTransportedDensity (q : Nat)
    (p : ErrorParameter) (firstPort secondPort : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q secondPort).conjDensity
    ((bh12SelectedPortSubsystem q secondPort).selectedPartialTraceFromRegister.mapDensity
      (depthTwoChildRun q p firstPort).acceptedOutput)
abbrev depthRawInputPath (q z : Nat) :=
  Fin z → Fin (bh12InputCount q)
abbrev depthOutputPath (q z : Nat) :=
  Fin z → OddRow q
def depthOutputPathPrefix (q z : Nat) (path : depthOutputPath q (z + 1)) :
    depthOutputPath q z :=
  fun i => path i.castSucc
def depthOutputPathLast (q z : Nat) (path : depthOutputPath q (z + 1)) :
    OddRow q :=
  path (Fin.last z)
noncomputable def bh12TotalNextParameter (q : Nat) (p : ErrorParameter)
    (port : OddRow q) : ErrorParameter :=
  dite (0 < rawSuccessMass q p)
    (fun hsuccess => bh12DecodedMarginalErrorParameter q p hsuccess port)
    (fun _ => p)
theorem bh12TotalNextParameter_of_success (q : Nat) (p : ErrorParameter)
    (port : OddRow q) (hsuccess : 0 < rawSuccessMass q p) :
    bh12TotalNextParameter q p port =
      bh12DecodedMarginalErrorParameter q p hsuccess port := by
  simp [bh12TotalNextParameter, hsuccess]
noncomputable def bh12PathParameter (q : Nat) (p : ErrorParameter) :
    (z : Nat) → depthOutputPath q z → ErrorParameter
  | 0, _ => p
  | z + 1, path =>
      bh12TotalNextParameter q
        (bh12PathParameter q p z (depthOutputPathPrefix q z path))
        (depthOutputPathLast q z path)
@[simp] theorem bh12PathParameter_zero (q : Nat) (p : ErrorParameter)
    (path : depthOutputPath q 0) :
    bh12PathParameter q p 0 path = p :=
  rfl
@[simp] theorem bh12PathParameter_succ (q z : Nat) (p : ErrorParameter)
    (path : depthOutputPath q (z + 1)) :
    bh12PathParameter q p (z + 1) path =
      bh12TotalNextParameter q
        (bh12PathParameter q p z (depthOutputPathPrefix q z path))
        (depthOutputPathLast q z path) :=
  rfl
theorem bh12PathParameter_admissible (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∀ (z : Nat) (path : depthOutputPath q z),
      (bh12InputCount q : ℝ) * (bh12PathParameter q p z path).rate ≤ 1 / 4 ∧
        (bh12PathParameter q p z path).rate ≤ 1 / 2 ∧
        quadraticCoefficient q * (bh12PathParameter q p z path).rate ≤ 1 := by
  intro z
  induction z with
  | zero =>
      intro path
      refine ⟨?_, ?_, hquadraticSmall⟩
      · exact hsmall
      · exact hhalf
  | succ z ih =>
      intro path
      obtain ⟨hpreviousSmall, hpreviousHalf, hpreviousCoefficient⟩ :=
        ih (depthOutputPathPrefix q z path)
      obtain ⟨hsuccess, _hactualSuccess, _hdensity, _hquadratic,
        _hnonincreasing, hnextSmall, hnextHalf, hnextCoefficient⟩ :=
        bh12OneStepPhysicalInvariant q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hpreviousSmall hpreviousHalf
          hpreviousCoefficient
      rw [bh12PathParameter_succ,
        bh12TotalNextParameter_of_success q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hsuccess]
      exact ⟨hnextSmall, hnextHalf, hnextCoefficient⟩
noncomputable def bh12PathNextResources (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    ResourceInput (bh12InputCount q) Qubit.QubitSpace :=
  depthTwoChildResources q (bh12PathParameter q p z path) port
noncomputable def bh12PathRun (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) :=
  bh12ActualRun q (bh12PathParameter q p z path)
noncomputable def bh12PathSelectedPortTransportedDensity (q : Nat)
    (p : ErrorParameter) (z : Nat) (path : depthOutputPath q z) (port : OddRow q) :
    DensityOperator Qubit.QubitSpace :=
  (bh12SelectedPortTransport q port).conjDensity
    ((bh12SelectedPortSubsystem q port).selectedPartialTraceFromRegister.mapDensity
      (bh12PathRun q p z path).acceptedOutput)
def bh12QuadraticEnvelope (q : Nat) (p : ErrorParameter) : Nat → ℝ
  | 0 => p.rate
  | z + 1 => quadraticCoefficient q * (bh12QuadraticEnvelope q p z) ^ 2
noncomputable def bh12QuadraticEnvelopeLogGrowthBase (q : Nat)
    (p : ErrorParameter) : ℝ :=
  -Real.log (quadraticCoefficient q * p.rate)
noncomputable def bh12QuadraticEnvelopeCostCoefficient (q : Nat)
    (p : ErrorParameter) : ℝ :=
  2 / Real.rpow (bh12QuadraticEnvelopeLogGrowthBase q p)
    (bh12BlockExponent q)
noncomputable def bh12PhysicalFlaggedBatch (q : Nat) (p : ErrorParameter) :
    DependentBatch.FiniteFlaggedBatch (OddRow q) (PhysicalError q) where
  weight := errorWordProbability p
  weight_nonneg := errorWordProbability_nonneg p
  total_weight := sum_errorWordProbability (Index := Column q) p
  accepted := fun error _ => decide (Accepts error)
noncomputable def bh12PhysicalFlaggedPool (q : Nat) (p : ErrorParameter)
    (count : Nat) :
    Fin count → DependentBatch.FiniteFlaggedBatch (OddRow q) (PhysicalError q) :=
  fun _ => bh12PhysicalFlaggedBatch q p
noncomputable def bh12OneLevelProtocolFamily (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) :
    DistillationProtocolFamily Qubit.QubitSpace (PhysicalRegister q)
      (LogicalRegister q) (OddRow q) where
  targetError := fun _ => quadraticCoefficient q * p.rate ^ 2
  protocol := fun port =>
    bh12MagicStateDistillationProtocol q p port
      (rawSuccessMass_pos_of_rate_le_half q p hhalf)
  outputResourceCount := fun _ => bh12OutputCount q
  outputResourceCount_pos := by
    intro port
    have hq : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hqzero
      subst q
      exact Fin.elim0 port.1
    change 0 < 2 * q
    omega
  successfulOutputError_le_targetError := by
    intro port
    exact bh12MagicStateDistillationProtocol_quadratic q p port hhalf
def bh12PathStage (q z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    depthOutputPath q stage.1 :=
  fun i => path ⟨i.1, lt_trans i.2 stage.2⟩
theorem bh12PathParameter_rate_le_geometric (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    ∀ (z : Nat) (path : depthOutputPath q z),
      (bh12PathParameter q p z path).rate ≤ p.rate / (2 : ℝ) ^ z := by
  have hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1 :=
    hstrong.trans (by norm_num)
  intro z
  induction z with
  | zero =>
      intro path
      simp
  | succ z ih =>
      intro path
      have hpreviousRate :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            p.rate / (2 : ℝ) ^ z :=
        ih (depthOutputPathPrefix q z path)
      have hpreviousLeInitial :
          (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            p.rate :=
        hpreviousRate.trans (div_le_self p.rate_nonneg
          (one_le_pow₀ (by norm_num)))
      obtain ⟨hpreviousSmall, hpreviousHalf, hpreviousCoefficient⟩ :=
        bh12PathParameter_admissible q p hsmall hhalf hquadraticSmall z
          (depthOutputPathPrefix q z path)
      obtain ⟨hsuccess, _hactualSuccess, _hdensity, hnextQuadratic,
        _hnonincreasing, _hnextSmall, _hnextHalf, _hnextCoefficient⟩ :=
        bh12OneStepPhysicalInvariant q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hpreviousSmall hpreviousHalf
          hpreviousCoefficient
      have hpreviousCoefficientHalf :
          quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ≤
            1 / 2 :=
        (mul_le_mul_of_nonneg_left hpreviousLeInitial
          (le_of_lt (quadraticCoefficient_pos q))).trans hstrong
      rw [bh12PathParameter_succ,
        bh12TotalNextParameter_of_success q
          (bh12PathParameter q p z (depthOutputPathPrefix q z path))
          (depthOutputPathLast q z path) hsuccess]
      calc
        (bh12DecodedMarginalErrorParameter q
            (bh12PathParameter q p z (depthOutputPathPrefix q z path)) hsuccess
            (depthOutputPathLast q z path)).rate ≤
            quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate ^ 2 :=
          hnextQuadratic
        _ = (quadraticCoefficient q *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate) *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate := by
          ring
        _ ≤ (1 / 2) *
              (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate :=
          mul_le_mul_of_nonneg_right hpreviousCoefficientHalf
            (bh12PathParameter q p z (depthOutputPathPrefix q z path)).rate_nonneg
        _ ≤ (1 / 2) * (p.rate / (2 : ℝ) ^ z) :=
          mul_le_mul_of_nonneg_left hpreviousRate (by norm_num)
        _ = p.rate / (2 : ℝ) ^ (z + 1) := by
          rw [pow_succ]
          field_simp [pow_ne_zero]
noncomputable def bh12PathYieldFactor (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) : ℝ :=
  rawSuccessMass q (bh12PathParameter q p stage.1
    (bh12PathStage q z path stage))
theorem bh12PathYieldFactor_lower (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) (stage : Fin z) :
    1 - 1 / (4 * (2 : ℝ) ^ stage.1) ≤
      bh12PathYieldFactor q p z path stage := by
  have hrate :
      (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
        p.rate / (2 : ℝ) ^ stage.1 :=
    bh12PathParameter_rate_le_geometric q p hsmall hhalf hstrong stage.1
      (bh12PathStage q z path stage)
  have hinput :
      (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
        1 / (4 * (2 : ℝ) ^ stage.1) := by
    calc
      (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate ≤
          (bh12InputCount q : ℝ) * (p.rate / (2 : ℝ) ^ stage.1) :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = ((bh12InputCount q : ℝ) * p.rate) / (2 : ℝ) ^ stage.1 := by
        ring
      _ ≤ (1 / 4) / (2 : ℝ) ^ stage.1 :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = 1 / (4 * (2 : ℝ) ^ stage.1) := by
        field_simp [pow_ne_zero]
  unfold bh12PathYieldFactor
  calc
    1 - 1 / (4 * (2 : ℝ) ^ stage.1) ≤
        1 - (bh12InputCount q : ℝ) *
          (bh12PathParameter q p stage.1 (bh12PathStage q z path stage)).rate := by
      linarith
    _ ≤ rawSuccessMass q (bh12PathParameter q p stage.1
          (bh12PathStage q z path stage)) :=
      rawSuccessMass_one_sub_inputCount_rate_le q
        (bh12PathParameter q p stage.1 (bh12PathStage q z path stage))
theorem bh12FiniteOneSubSum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ i ∈ s, 0 ≤ loss i)
    (hlossLeOne : ∀ i ∈ s, loss i ≤ 1) :
    1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsumNonneg : 0 ≤ ∑ i ∈ s, loss i :=
        Finset.sum_nonneg fun i hi =>
          hlossNonneg i (Finset.mem_insert_of_mem hi)
      have hrest :
          1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) :=
        ih (fun i hi => hlossNonneg i (Finset.mem_insert_of_mem hi))
          (fun i hi => hlossLeOne i (Finset.mem_insert_of_mem hi))
      calc
        1 - (loss a + ∑ i ∈ s, loss i) ≤
            (1 - loss a) * (1 - ∑ i ∈ s, loss i) := by
          nlinarith [hlossNonneg a (Finset.mem_insert_self a s)]
        _ ≤ (1 - loss a) * ∏ i ∈ s, (1 - loss i) :=
          mul_le_mul_of_nonneg_left hrest (by
            linarith [hlossLeOne a (Finset.mem_insert_self a s)])
theorem bh12GeometricLossSum_le_half (z : Nat) :
    (∑ stage : Fin z, 1 / (4 * (2 : ℝ) ^ stage.1)) ≤ 1 / 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ i ∈ Finset.range z,
        if h : i < z then 1 / (4 * (2 : ℝ) ^ i) else 0) =
        (∑ i ∈ Finset.range z, 1 / (4 * (2 : ℝ) ^ i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos hi]
    _ =
        (1 / 4) * ∑ i ∈ Finset.range z, (1 / (2 : ℝ)) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [div_pow, pow_ne_zero]
      rw [← mul_pow]
      norm_num
    _ ≤ (1 / 4) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le z) (by norm_num)
    _ = 1 / 2 := by norm_num
noncomputable def bh12PathYieldFactorProduct (q : Nat) (p : ErrorParameter)
    (z : Nat) (path : depthOutputPath q z) : ℝ :=
  ∏ stage : Fin z, bh12PathYieldFactor q p z path stage
theorem bh12PathYieldFactorProduct_half_le (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    (1 : ℝ) / 2 ≤ bh12PathYieldFactorProduct q p z path := by
  let loss : Fin z → ℝ := fun stage => 1 / (4 * (2 : ℝ) ^ stage.1)
  have hlossNonneg (stage : Fin z) : 0 ≤ loss stage := by
    dsimp [loss]
    positivity
  have hlossLeOne (stage : Fin z) : loss stage ≤ 1 := by
    have hpow : 1 ≤ (2 : ℝ) ^ stage.1 := one_le_pow₀ (by norm_num)
    have hdenomPos : 0 < 4 * (2 : ℝ) ^ stage.1 := by positivity
    dsimp [loss]
    apply (div_le_iff₀ hdenomPos).2
    nlinarith
  have hproductLower :
      1 - ∑ stage : Fin z, loss stage ≤
        ∏ stage : Fin z, bh12PathYieldFactor q p z path stage := by
    calc
      1 - ∑ stage : Fin z, loss stage ≤ ∏ stage : Fin z, (1 - loss stage) := by
        simpa using (bh12FiniteOneSubSum_le_product Finset.univ loss
          (fun stage _ => hlossNonneg stage)
          (fun stage _ => hlossLeOne stage))
      _ ≤ ∏ stage : Fin z, bh12PathYieldFactor q p z path stage := by
        refine Finset.prod_le_prod ?_ ?_
        · intro stage _
          linarith [hlossLeOne stage]
        · intro stage _
          dsimp [loss]
          exact bh12PathYieldFactor_lower q p hsmall hhalf hstrong z path stage
  have hsum : ∑ stage : Fin z, loss stage ≤ 1 / 2 := by
    simpa [loss] using bh12GeometricLossSum_le_half z
  unfold bh12PathYieldFactorProduct
  linarith
theorem bh12PathYieldFactorProduct_pos (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) :
    0 < bh12PathYieldFactorProduct q p z path := by
  exact lt_of_lt_of_le (by norm_num)
    (bh12PathYieldFactorProduct_half_le q p hsmall hhalf hstrong z path)
noncomputable def bh12PathTypedYieldFactor (q : Nat) (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) : NNReal :=
  ⟨bh12PathYieldFactorProduct q p z path,
    (bh12PathYieldFactorProduct_pos q p hsmall hhalf hstrong z path).le⟩
noncomputable def bh12PathTypedSuccessfulOutputCost (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (z : Nat) (path : depthOutputPath q z) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (depthRawInputPath q z)
    (depthOutputPath q z)
    (bh12PathTypedYieldFactor q p hsmall hhalf hstrong z path)
structure BH12PathScheduleIndex (q : Nat) where
  depth : Nat
  path : depthOutputPath q depth
def bh12PathScheduleIndex_succ (q z : Nat) (path : depthOutputPath q (z + 1)) :
    BH12PathScheduleIndex q where
  depth := z + 1
  path := path
abbrev bh12PathScheduleInputSlots (q : Nat) (index : BH12PathScheduleIndex q) :=
  depthRawInputPath q index.depth
abbrev bh12PathScheduleOutputSlots (q : Nat) (index : BH12PathScheduleIndex q) :=
  depthOutputPath q index.depth
def bh12PathScheduleTargetError (q : Nat) (p : ErrorParameter)
    (index : BH12PathScheduleIndex q) : ℝ :=
  bh12QuadraticEnvelope q p index.depth
noncomputable def bh12PathScheduleTypedYieldFactor (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) : NNReal :=
  bh12PathTypedYieldFactor q p hsmall hhalf hstrong index.depth index.path
noncomputable def bh12PathScheduleTypedSuccessfulOutputCost (q : Nat)
    (p : ErrorParameter)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2)
    (index : BH12PathScheduleIndex q) : ℝ :=
  DependentBatch.typedSuccessfulOutputCost (bh12PathScheduleInputSlots q index)
    (bh12PathScheduleOutputSlots q index)
    (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong index)
end QEC.Distillation.Triorthogonal.BH12Concatenation


