-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
-- name    : QEC_Distillation_Triorthogonal_NoisyInjection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:25:14.46957+00:00
-- url     : https://prove2.me/theorems/8ef8c121-0057-4f51-8182-92eabbe86bfa
-- title:
--   Noisy Injection
-- statement:
--   Definitions and structural lemmas for Noisy Injection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_complete_of_adjoint_square_sum
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_square
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
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
namespace Triorthogonal
namespace BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
structure ErrorParameter where
  rate : ℝ
  rate_nonneg : 0 ≤ rate
  rate_le_one : rate ≤ 1
namespace ErrorParameter
def cleanWeight (p : ErrorParameter) : ℝ := 1 - p.rate
theorem cleanWeight_nonneg (p : ErrorParameter) : 0 ≤ p.cleanWeight :=
  sub_nonneg.mpr p.rate_le_one
theorem cleanWeight_le_one (p : ErrorParameter) : p.cleanWeight ≤ 1 := by
  dsimp [cleanWeight]
  linarith [p.rate_nonneg]
theorem cleanWeight_add_rate (p : ErrorParameter) :
    p.cleanWeight + p.rate = 1 := by
  simp [cleanWeight]
end ErrorParameter
namespace OneQubit
open Semantics.Qubit
open OneQubitMagic
def zLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk pauliZ pauliZ
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)
@[simp] theorem zLinearEquiv_apply (psi : QubitSpace) :
    zLinearEquiv psi = pauliZ psi :=
  rfl
@[simp] theorem zLinearEquiv_symm_apply (psi : QubitSpace) :
    zLinearEquiv.symm psi = pauliZ psi :=
  rfl
theorem pauliZ_map_inner (psi phi : QubitSpace) :
    inner Complex (pauliZ psi) (pauliZ phi) = inner Complex psi phi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, pauliZ_apply, RCLike.inner_apply, map_mul]
  ring_nf
  simp
def zTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := zLinearEquiv
  map_inner := pauliZ_map_inner
def aZeroState : QubitSpace :=
  phaseState (Real.pi / 4)
def aOneState : QubitSpace :=
  zTransport aZeroState
@[simp] theorem aOneState_eq_pauliZ :
    aOneState = pauliZ aZeroState :=
  rfl
@[simp] theorem aZeroState_norm : ‖aZeroState‖ = 1 := by
  exact phaseState_norm (Real.pi / 4)
@[simp] theorem aOneState_norm : ‖aOneState‖ = 1 := by
  change ‖zTransport.toLinearIsometryEquiv aZeroState‖ = 1
  rw [zTransport.toLinearIsometryEquiv.norm_map, aZeroState_norm]
def aZeroDensity : DensityOperator QubitSpace :=
  phaseStateDensity (Real.pi / 4)
def aOneDensity : DensityOperator QubitSpace :=
  zTransport.conjDensity aZeroDensity
@[simp] theorem aOneDensity_toOperator :
    aOneDensity.toOperator =
      pauliZ.comp (aZeroDensity.toOperator.comp pauliZ) := by
  rw [aOneDensity, UnitaryTransport.conjDensity_toOperator]
  ext psi
  rfl
def diagonalAResource (p : ErrorParameter) : DensityOperator QubitSpace :=
  outcomeMixture p.cleanWeight p.cleanWeight_nonneg p.cleanWeight_le_one
    aZeroDensity aOneDensity
@[simp] theorem diagonalAResource_toOperator (p : ErrorParameter) :
    (diagonalAResource p).toOperator =
      p.cleanWeight • aZeroDensity.toOperator +
        p.rate • aOneDensity.toOperator := by
  simp [diagonalAResource, outcomeMixture,
    DensityOperator.convexCombinationOperator, branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {DistillationOutcome.accepted, DistillationOutcome.rejected} by decide,
    ErrorParameter.cleanWeight]
def composeTransport
    (after before : UnitaryTransport QubitSpace QubitSpace) :
    UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := before.toLinearEquiv.trans after.toLinearEquiv
  map_inner := by
    intro psi phi
    change inner Complex (after (before psi)) (after (before phi)) =
      inner Complex psi phi
    rw [after.map_inner, before.map_inner]
def idealTTransport : UnitaryTransport QubitSpace QubitSpace :=
  phaseShiftTransport (Real.pi / 4)
def aBasisTransport : UnitaryTransport QubitSpace QubitSpace :=
  composeTransport idealTTransport hadamardTransport
@[simp] theorem aBasisTransport_basis_zero :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      aZeroState := by
  ext bit
  fin_cases bit
  all_goals simp [aBasisTransport, composeTransport, idealTTransport,
    hadamardTransport, aZeroState, phaseState]
  all_goals ring
@[simp] theorem aBasisTransport_basis_one :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      aOneState := by
  ext bit
  fin_cases bit
  all_goals simp [aBasisTransport, composeTransport, idealTTransport,
    hadamardTransport, aOneState, aZeroState, phaseState, zTransport,
    zLinearEquiv]
  all_goals ring
def aBasisObservable : Operator QubitSpace :=
  aBasisTransport.conjOperator pauliZ
theorem aBasisObservable_adjoint :
    LinearMap.adjoint aBasisObservable = aBasisObservable := by
  rw [aBasisObservable, UnitaryTransport.conjOperator_adjoint, pauliZ_adjoint]
theorem aBasisObservable_square :
    aBasisObservable * aBasisObservable = 1 := by
  rw [aBasisObservable, ← UnitaryTransport.conjOperator_mul, pauliZ_square]
  exact aBasisTransport.conjOperator_one
@[simp] theorem aBasisObservable_aZeroState :
    aBasisObservable aZeroState = aZeroState := by
  rw [← aBasisTransport_basis_zero]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      EuclideanSpace.basisFun (Fin 2) Complex 0 := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz]
@[simp] theorem aBasisObservable_aOneState :
    aBasisObservable aOneState = -aOneState := by
  rw [← aBasisTransport_basis_one]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      -(EuclideanSpace.basisFun (Fin 2) Complex 1) := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz, map_neg]
def aBasisProjector (outcome : StabilizerOutcome) : Operator QubitSpace :=
  (1 / 2 : Complex) •
    (1 + outcome.sign • aBasisObservable)
theorem aBasisProjector_adjoint (outcome : StabilizerOutcome) :
    LinearMap.adjoint (aBasisProjector outcome) = aBasisProjector outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold aBasisProjector
  apply LinearMap.IsSymmetric.smul
  · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) =
        (2 : Complex)⁻¹ := by
      rw [map_inv₀]
      have htwo : starRingEnd Complex (2 : Complex) = 2 :=
        map_natCast (starRingEnd Complex) 2
      rw [htwo]
    simpa only [one_div] using hreal
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · apply LinearMap.IsSymmetric.smul
      · cases outcome <;> simp [StabilizerOutcome.sign]
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact aBasisObservable_adjoint
theorem aBasisProjector_idempotent (outcome : StabilizerOutcome) :
    aBasisProjector outcome * aBasisProjector outcome =
      aBasisProjector outcome := by
  cases outcome <;>
    simp only [aBasisProjector, StabilizerOutcome.sign,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      aBasisObservable_square] <;>
    module
theorem aBasisProjector_add :
    aBasisProjector .positive + aBasisProjector .negative = 1 := by
  simp only [aBasisProjector, StabilizerOutcome.sign]
  module
@[simp] theorem aBasisProjector_positive_aZeroState :
    aBasisProjector .positive aZeroState = aZeroState := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    one_smul, aBasisObservable_aZeroState]
  module
@[simp] theorem aBasisProjector_negative_aZeroState :
    aBasisProjector .negative aZeroState = 0 := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    aBasisObservable_aZeroState]
  module
@[simp] theorem aBasisProjector_positive_aOneState :
    aBasisProjector .positive aOneState = 0 := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    one_smul, aBasisObservable_aOneState]
  module
@[simp] theorem aBasisProjector_negative_aOneState :
    aBasisProjector .negative aOneState = aOneState := by
  simp only [aBasisProjector, StabilizerOutcome.sign,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    aBasisObservable_aOneState]
  module
@[simp] theorem aBasisProjector_positive_pauliZ_aZeroState :
    aBasisProjector .positive (pauliZ aZeroState) = 0 := by
  rw [← aOneState_eq_pauliZ]
  exact aBasisProjector_positive_aOneState
@[simp] theorem aBasisProjector_negative_pauliZ_aZeroState :
    aBasisProjector .negative (pauliZ aZeroState) = pauliZ aZeroState := by
  rw [← aOneState_eq_pauliZ]
  exact aBasisProjector_negative_aOneState
def aBasisDephasingKrausFamily :
    FiniteKrausFamily StabilizerOutcome QubitSpace QubitSpace where
  operator := aBasisProjector
theorem aBasisDephasingKrausFamily_complete :
    aBasisDephasingKrausFamily.Complete := by
  unfold FiniteKrausFamily.Complete
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      aBasisProjector outcome * aBasisProjector outcome) = 1
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  simpa [aBasisProjector_idempotent] using aBasisProjector_add
def aBasisDephasing : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasingKrausFamily.toQuantumChannel
    aBasisDephasingKrausFamily_complete
def aBasisInstrument :
    FiniteInstrument StabilizerOutcome StabilizerOutcome QubitSpace QubitSpace where
  kraus := aBasisDephasingKrausFamily
  observe := id
noncomputable def aBasisBranchLinearMap
    (outcome : StabilizerOutcome) :
    Operator QubitSpace →ₗ[Complex] Operator QubitSpace where
  toFun := aBasisInstrument.branchOperator outcome
  map_add' := by
    intro A B
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : aBasisInstrument.observe index = outcome
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
    intro index _
    by_cases hobserve : aBasisInstrument.observe index = outcome
    · simp only [hobserve, if_true]
      apply LinearMap.ext
      intro psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]
def aBasisTwirl : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasing
def zAfterTTransport : UnitaryTransport QubitSpace QubitSpace :=
  composeTransport zTransport idealTTransport
def injectionBranchTransport (error : Fin 2) :
    UnitaryTransport QubitSpace QubitSpace :=
  if error = 0 then idealTTransport else zAfterTTransport
def branchProbability (p : ErrorParameter) (error : Fin 2) : ℝ :=
  if error = 0 then p.cleanWeight else p.rate
theorem branchProbability_nonneg (p : ErrorParameter) (error : Fin 2) :
    0 ≤ branchProbability p error := by
  by_cases h : error = 0
  · simp [branchProbability, h, p.cleanWeight_nonneg]
  · simp [branchProbability, h, p.rate_nonneg]
def branchAmplitude (p : ErrorParameter) (error : Fin 2) : Complex :=
  (Real.sqrt (branchProbability p error) : Complex)
theorem branchAmplitude_normSq (p : ErrorParameter) (error : Fin 2) :
    star (branchAmplitude p error) * branchAmplitude p error =
      (branchProbability p error : Complex) := by
  rw [show star (branchAmplitude p error) = branchAmplitude p error by
    apply Complex.ext <;> simp [branchAmplitude]]
  change (Real.sqrt (branchProbability p error) : Complex) *
      (Real.sqrt (branchProbability p error) : Complex) =
    (branchProbability p error : Complex)
  rw [← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex))
    (Real.mul_self_sqrt (branchProbability_nonneg p error))
def injectionUnitaryFamily :
    FiniteKrausFamily (Fin 2) QubitSpace QubitSpace where
  operator error := (injectionBranchTransport error).toLinearEquiv.toLinearMap
theorem injectionUnitaryFamily_adjoint_comp (error : Fin 2) :
    (LinearMap.adjoint (injectionUnitaryFamily.operator error)).comp
        (injectionUnitaryFamily.operator error) = 1 := by
  change (LinearMap.adjoint
      (injectionBranchTransport error).toLinearEquiv.toLinearMap).comp
      (injectionBranchTransport error).toLinearEquiv.toLinearMap = 1
  rw [(injectionBranchTransport error).adjoint_toLinearMap]
  ext psi
  simp
def noisyTKrausFamily (p : ErrorParameter) :
    FiniteKrausFamily (Fin 2) QubitSpace QubitSpace :=
  injectionUnitaryFamily.scale (branchAmplitude p)
theorem noisyTKrausFamily_complete (p : ErrorParameter) :
    (noisyTKrausFamily p).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, branchAmplitude_normSq,
    injectionUnitaryFamily_adjoint_comp]
  ext psi site
  simp [branchProbability, ErrorParameter.cleanWeight]
  ring
def noisyTChannel (p : ErrorParameter) : QuantumChannel QubitSpace QubitSpace :=
  (noisyTKrausFamily p).toQuantumChannel (noisyTKrausFamily_complete p)
def resourceConsumption : Nat := 1
theorem noisyTChannel_apply (p : ErrorParameter) (A : Operator QubitSpace) :
    noisyTChannel p A =
      (p.cleanWeight : Complex) •
          idealTTransport.conjOperator A +
        (p.rate : Complex) •
          zTransport.conjOperator (idealTTransport.conjOperator A) := by
  rw [noisyTChannel, FiniteKrausFamily.toQuantumChannel_apply_sum]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, noisyTKrausFamily, FiniteKrausFamily.scale_operator]
  rw [show branchAmplitude p 0 • injectionUnitaryFamily.operator 0 =
      branchAmplitude p 0 • idealTTransport.toLinearEquiv.toLinearMap by rfl]
  rw [show branchAmplitude p 1 • injectionUnitaryFamily.operator 1 =
      branchAmplitude p 1 • zAfterTTransport.toLinearEquiv.toLinearMap by rfl]
  have hadjointTransport (amplitude : Complex)
      (U : UnitaryTransport QubitSpace QubitSpace) :
      LinearMap.adjoint (amplitude • U.toLinearEquiv.toLinearMap) =
        star amplitude • LinearMap.adjoint U.toLinearEquiv.toLinearMap := by
    exact map_smulₛₗ
      (LinearMap.adjoint :
        (QubitSpace →ₗ[Complex] QubitSpace) ≃ₗ⋆[Complex]
          (QubitSpace →ₗ[Complex] QubitSpace))
      amplitude U.toLinearEquiv.toLinearMap
  rw [hadjointTransport (branchAmplitude p 0) idealTTransport,
    hadjointTransport (branchAmplitude p 1) zAfterTTransport]
  rw [idealTTransport.adjoint_toLinearMap,
    zAfterTTransport.adjoint_toLinearMap]
  ext psi
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_smul]
  rw [branchAmplitude_normSq p 0, branchAmplitude_normSq p 1]
  simp [UnitaryTransport.conjOperator, zAfterTTransport, composeTransport,
    branchProbability, LinearMap.comp_apply]
@[simp] theorem noisyTChannel_mapDensity_toOperator
    (p : ErrorParameter) (rho : DensityOperator QubitSpace) :
    ((noisyTChannel p).mapDensity rho).toOperator =
      (p.cleanWeight : Complex) •
          idealTTransport.conjOperator rho.toOperator +
        (p.rate : Complex) •
          zTransport.conjOperator
            (idealTTransport.conjOperator rho.toOperator) := by
  exact noisyTChannel_apply p rho.toOperator
end OneQubit
section Register
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
def errorWordProbability (p : ErrorParameter)
    (error : Word (ZMod 2) Index) : ℝ :=
  ∏ site, if error site = 0 then p.cleanWeight else p.rate
omit [DecidableEq Index] in
theorem errorWordProbability_nonneg (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    0 ≤ errorWordProbability p error := by
  exact Finset.prod_nonneg fun site _ => by
    by_cases h : error site = 0
    · simp [h, p.cleanWeight_nonneg]
    · simp [h, p.rate_nonneg]
theorem sum_errorWordProbability (p : ErrorParameter) :
    ∑ error : Word (ZMod 2) Index, errorWordProbability p error = 1 := by
  classical
  have h := Finset.sum_prod_piFinset
    (R := ℝ) (ι := Index) (κ := ZMod 2)
    (s := Finset.univ)
    (g := fun _ bit => if bit = 0 then p.cleanWeight else p.rate)
  have hbit :
      ∑ bit : ZMod 2, (if bit = 0 then p.cleanWeight else p.rate) = 1 := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    simp [p.cleanWeight_add_rate]
  rw [hbit] at h
  simpa [errorWordProbability] using h
def registerBranchOperator (error : Word (ZMod 2) Index) :
    Operator (Qubit.QubitRegister Index) :=
  (toQubitOperator (cssZCheck error)).comp
    (allSiteT (Index := Index)).toLinearEquiv.toLinearMap
theorem registerBranchOperator_adjoint_comp
    (error : Word (ZMod 2) Index) :
    (LinearMap.adjoint (registerBranchOperator error)).comp
        (registerBranchOperator error) = 1 := by
  let T := (allSiteT (Index := Index)).toLinearEquiv.toLinearMap
  let Z := toQubitOperator (cssZCheck error)
  change (LinearMap.adjoint (Z.comp T)).comp (Z.comp T) = 1
  rw [LinearMap.adjoint_comp]
  calc
    ((LinearMap.adjoint T).comp (LinearMap.adjoint Z)).comp (Z.comp T) =
        (LinearMap.adjoint T).comp
          (((LinearMap.adjoint Z).comp Z).comp T) := by
      ext psi
      rfl
    _ = (LinearMap.adjoint T).comp T := by
      rw [show (LinearMap.adjoint Z).comp Z = 1 by
        exact toQubitOperator_adjoint_comp_self (cssZCheck error)]
      ext psi
      rfl
    _ = 1 := by
      dsimp [T]
      rw [(allSiteT (Index := Index)).adjoint_toLinearMap]
      ext psi
      simp
def errorWordAmplitude (p : ErrorParameter)
    (error : Word (ZMod 2) Index) : Complex :=
  (Real.sqrt (errorWordProbability p error) : Complex)
omit [DecidableEq Index] in
theorem errorWordAmplitude_normSq (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    star (errorWordAmplitude p error) * errorWordAmplitude p error =
      (errorWordProbability p error : Complex) := by
  rw [show star (errorWordAmplitude p error) = errorWordAmplitude p error by
    apply Complex.ext <;> simp [errorWordAmplitude]]
  change (Real.sqrt (errorWordProbability p error) : Complex) *
      (Real.sqrt (errorWordProbability p error) : Complex) =
    (errorWordProbability p error : Complex)
  rw [← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : Complex))
    (Real.mul_self_sqrt (errorWordProbability_nonneg p error))
def registerUnitaryFamily :
    FiniteKrausFamily (Word (ZMod 2) Index)
      (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) where
  operator := registerBranchOperator
def independentNoisyTKrausFamily (p : ErrorParameter) :
    FiniteKrausFamily (Word (ZMod 2) Index)
      (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  registerUnitaryFamily.scale (errorWordAmplitude p)
theorem independentNoisyTKrausFamily_complete (p : ErrorParameter) :
    (independentNoisyTKrausFamily (Index := Index) p).Complete := by
  apply FiniteKrausFamily.scale_complete_of_adjoint_square_sum
  simp_rw [errorWordAmplitude_normSq, registerUnitaryFamily,
    registerBranchOperator_adjoint_comp]
  rw [← Finset.sum_smul]
  have hsum :
      ∑ error : Word (ZMod 2) Index,
        (errorWordProbability p error : Complex) = 1 := by
    exact_mod_cast sum_errorWordProbability (Index := Index) p
  rw [hsum]
  simp
def independentNoisyTChannel (p : ErrorParameter) :
    QuantumChannel (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  (independentNoisyTKrausFamily (Index := Index) p).toQuantumChannel
    (independentNoisyTKrausFamily_complete p)
end Register
end BH12NoisyInjection
end Triorthogonal
end Distillation
end QEC


