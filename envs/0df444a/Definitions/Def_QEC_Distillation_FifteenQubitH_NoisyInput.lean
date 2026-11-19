-- Prove2me | Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
-- name    : QEC_Distillation_FifteenQubitH_NoisyInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:10.804348+00:00
-- url     : https://prove2.me/theorems/6d9f83bc-e668-4f72-a41a-e1dee752d70e
-- title:
--   Noisy Input
-- statement:
--   Definitions and structural lemmas for Noisy Input, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
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
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_adjoint
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_square
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
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


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite
theorem densityOperator_ext_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
noncomputable def sourceA0Transport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseTransport.toLinearEquiv.symm.trans
    hadamardTransport.toLinearEquiv
  map_inner := by
    intro x y
    exact (hadamardTransport.map_inner (phaseTransport.symm x)
      (phaseTransport.symm y)).trans (phaseTransport.symm.map_inner x y)
@[simp] theorem sourceA0Transport_apply (psi : QubitSpace) :
    sourceA0Transport psi = hadamardOperator (phaseInverseOperator psi) :=
  rfl
noncomputable def sourceA0Density : DensityOperator QubitSpace :=
  sourceA0Transport.conjDensity hMagicState
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
def aZeroState : QubitSpace := phaseState (Real.pi / 4)
def aOneState : QubitSpace := zTransport aZeroState
@[simp] theorem aOneState_eq_pauliZ : aOneState = pauliZ aZeroState :=
  rfl
@[simp] theorem aZeroState_norm : ‖aZeroState‖ = 1 := by
  exact phaseState_norm (Real.pi / 4)
@[simp] theorem aOneState_norm : ‖aOneState‖ = 1 := by
  change ‖zTransport.toLinearIsometryEquiv aZeroState‖ = 1
  rw [zTransport.toLinearIsometryEquiv.norm_map, aZeroState_norm]
noncomputable def aZeroDensity : DensityOperator QubitSpace := sourceA0Density
noncomputable def aOneDensity : DensityOperator QubitSpace :=
  zTransport.conjDensity aZeroDensity
noncomputable def aBasisTransport : UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans (phaseShiftTransport (Real.pi / 4))
@[simp] theorem aBasisTransport_basis_zero :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 0) = aZeroState := by
  ext bit
  fin_cases bit
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 0)) 0 =
      phaseState (Real.pi / 4) 0
    rw [phaseShiftOperator_apply_zero, hadamardOperator_apply_zero,
      phaseState_apply_zero]
    simp
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 0)) 1 =
      phaseState (Real.pi / 4) 1
    rw [phaseShiftOperator_apply_one, hadamardOperator_apply_one,
      phaseState_apply_one]
    simp <;> ring
@[simp] theorem aBasisTransport_basis_one :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 1) = aOneState := by
  ext bit
  fin_cases bit
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 1)) 0 =
      pauliZ (phaseState (Real.pi / 4)) 0
    rw [phaseShiftOperator_apply_zero, hadamardOperator_apply_zero,
      pauliZ_apply, zPhase, phaseState_apply_zero]
    simp
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 1)) 1 =
      pauliZ (phaseState (Real.pi / 4)) 1
    rw [phaseShiftOperator_apply_one, hadamardOperator_apply_one,
      pauliZ_apply, zPhase, phaseState_apply_one]
    simp <;> ring
def aBasisObservable : Operator QubitSpace := aBasisTransport.conjOperator pauliZ
def sourceAObservable : Operator QubitSpace :=
  (Real.sqrt 2 : Complex)⁻¹ • (pauliX + pauliY)
theorem aBasisObservable_adjoint :
    LinearMap.adjoint aBasisObservable = aBasisObservable := by
  rw [aBasisObservable, UnitaryTransport.conjOperator_adjoint, pauliZ_adjoint]
theorem aBasisObservable_square : aBasisObservable * aBasisObservable = 1 := by
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
def aBasisProjector
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) : Operator QubitSpace :=
  (1 / 2 : Complex) • (1 + outcome.sign • aBasisObservable)
theorem aBasisProjector_adjoint
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    LinearMap.adjoint (aBasisProjector outcome) = aBasisProjector outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold aBasisProjector
  apply LinearMap.IsSymmetric.smul
  · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
      rw [map_inv₀]
      have htwo : starRingEnd Complex (2 : Complex) = 2 :=
        map_natCast (starRingEnd Complex) 2
      rw [htwo]
    simpa only [one_div] using hreal
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · apply LinearMap.IsSymmetric.smul
      · cases outcome <;>
          simp [Coding.PauliSymplectic.StabilizerOutcome.sign]
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact aBasisObservable_adjoint
theorem aBasisProjector_idempotent
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    aBasisProjector outcome * aBasisProjector outcome = aBasisProjector outcome := by
  cases outcome <;>
    simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      smul_mul_assoc,
      mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      aBasisObservable_square] <;>
    module
theorem aBasisProjector_add :
    aBasisProjector Coding.PauliSymplectic.StabilizerOutcome.positive +
      aBasisProjector Coding.PauliSymplectic.StabilizerOutcome.negative = 1 := by
  simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign]
  module
def aBasisDephasingKrausFamily :
    FiniteKrausFamily Coding.PauliSymplectic.StabilizerOutcome QubitSpace QubitSpace where
  operator := aBasisProjector
theorem aBasisDephasingKrausFamily_complete :
    aBasisDephasingKrausFamily.Complete := by
  unfold FiniteKrausFamily.Complete
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change (∑ outcome : Coding.PauliSymplectic.StabilizerOutcome,
    aBasisProjector outcome * aBasisProjector outcome) = 1
  rw [show (Finset.univ : Finset Coding.PauliSymplectic.StabilizerOutcome) =
      {Coding.PauliSymplectic.StabilizerOutcome.positive,
        Coding.PauliSymplectic.StabilizerOutcome.negative} by decide]
  simpa [aBasisProjector_idempotent] using aBasisProjector_add
def aBasisDephasing : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasingKrausFamily.toQuantumChannel aBasisDephasingKrausFamily_complete
def hStep (d : HDirection) : HDirection := hadamardClifford • d
def sStep (d : HDirection) : HDirection := phaseClifford • d
noncomputable def hCanonicalizerCandidate : Fin 12 →
    UnitaryTransport QubitSpace QubitSpace
  | 0 => phaseTransport.trans (phaseTransport.trans phaseTransport)
  | 1 => hadamardTransport.trans
      (phaseTransport.trans (phaseTransport.trans
        (hadamardTransport.trans phaseTransport)))
  | 2 => phaseTransport
  | 3 => phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport))
  | 4 => UnitaryTransport.identity QubitSpace
  | 5 => hadamardTransport.trans (phaseTransport.trans phaseTransport)
  | 6 => phaseTransport.trans phaseTransport
  | 7 => phaseTransport.trans (phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport)))
  | 8 => hadamardTransport.trans phaseTransport
  | 9 => phaseTransport.trans (hadamardTransport.trans phaseTransport)
  | 10 => hadamardTransport.trans (phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport)))
  | 11 => phaseTransport.trans
      (phaseTransport.trans (hadamardTransport.trans phaseTransport))
def hCanonicalizerTarget : Fin 12 → HDirection → HDirection
  | 0 => fun d => sStep (sStep (sStep d))
  | 1 => fun d => sStep (hStep (sStep (sStep (hStep d))))
  | 2 => fun d => sStep d
  | 3 => fun d => sStep (sStep (hStep (sStep d)))
  | 4 => fun d => d
  | 5 => fun d => sStep (sStep (hStep d))
  | 6 => fun d => sStep (sStep d)
  | 7 => fun d => sStep (sStep (hStep (sStep (sStep d))))
  | 8 => fun d => sStep (hStep d)
  | 9 => fun d => sStep (hStep (sStep d))
  | 10 => fun d => sStep (sStep (hStep (sStep (hStep d))))
  | 11 => fun d => sStep (hStep (sStep (sStep d)))
theorem hCanonicalizerCandidate_complete (d : HDirection) :
    ∃ i : Fin 12, hCanonicalizerTarget i d = hReference := by
  revert d
  decide +kernel
noncomputable def hCanonicalizerIndex (d : HDirection) : Fin 12 :=
  Classical.choose (hCanonicalizerCandidate_complete d)
noncomputable def hCanonicalizer (d : HDirection) :
    UnitaryTransport QubitSpace QubitSpace :=
  hCanonicalizerCandidate (hCanonicalizerIndex d)
def hInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (hProjector hReference) rho
def hInputFidelity (rho : DensityOperator QubitSpace) : Real :=
  hDirectionFidelity rho hReference
def hInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - hInputSquaredOverlap rho
noncomputable def hCanonicalizedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (hCanonicalizer (hMaximizingDirection rho)).conjDensity rho
noncomputable def sourceAFramedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  sourceA0Transport.conjDensity (hCanonicalizedInput rho)
def aInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (aBasisProjector .positive) rho
def aInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - aInputSquaredOverlap rho
structure BK15Epsilon where
  epsilon : Real
  nonneg : 0 ≤ epsilon
  le_half : epsilon ≤ 1 / 2
namespace BK15Epsilon
theorem le_one (epsilon : BK15Epsilon) : epsilon.epsilon ≤ 1 := by
  linarith [epsilon.le_half]
def cleanWeight (epsilon : BK15Epsilon) : Real := 1 - epsilon.epsilon
theorem cleanWeight_nonneg (epsilon : BK15Epsilon) : 0 ≤ epsilon.cleanWeight :=
  sub_nonneg.mpr epsilon.le_one
theorem cleanWeight_add_error (epsilon : BK15Epsilon) :
    epsilon.cleanWeight + epsilon.epsilon = 1 := by
  simp [cleanWeight]
end BK15Epsilon
noncomputable def aInputComponent : Fin 2 → DensityOperator QubitSpace
  | 0 => aZeroDensity
  | 1 => aOneDensity
def aInputWeight (epsilon : BK15Epsilon) : Fin 2 → Real
  | 0 => epsilon.cleanWeight
  | 1 => epsilon.epsilon
theorem aInputWeight_nonneg (epsilon : BK15Epsilon) (bit : Fin 2) :
    0 ≤ aInputWeight epsilon bit := by
  fin_cases bit
  · exact epsilon.cleanWeight_nonneg
  · exact epsilon.nonneg
theorem sum_aInputWeight (epsilon : BK15Epsilon) :
    ∑ bit : Fin 2, aInputWeight epsilon bit = 1 := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [aInputWeight, epsilon.cleanWeight_add_error]
noncomputable def diagonalAResource (epsilon : BK15Epsilon) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ (aInputWeight epsilon) aInputComponent
    (by
      intro bit _hbit
      exact aInputWeight_nonneg epsilon bit)
    (by simpa using sum_aInputWeight epsilon)
noncomputable def hCanonicalizedInputEpsilon
    (rho : DensityOperator QubitSpace) (hpositive : 0 < 1 - hFidelity rho ^ 2)
    (hleHalf : 1 - hFidelity rho ^ 2 ≤ 1 / 2) : BK15Epsilon where
  epsilon := 1 - hFidelity rho ^ 2
  nonneg := hpositive.le
  le_half := hleHalf
noncomputable def hCanonicalizedDephasedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity (sourceAFramedInput rho)
abbrev BK1Tensor := QubitSpace
abbrev BK2Tensor := CompositeSystem QubitSpace BK1Tensor
abbrev BK3Tensor := CompositeSystem QubitSpace BK2Tensor
abbrev BK4Tensor := CompositeSystem QubitSpace BK3Tensor
abbrev BK5Tensor := CompositeSystem QubitSpace BK4Tensor
abbrev BK6Tensor := CompositeSystem QubitSpace BK5Tensor
abbrev BK7Tensor := CompositeSystem QubitSpace BK6Tensor
abbrev BK8Tensor := CompositeSystem QubitSpace BK7Tensor
abbrev BK9Tensor := CompositeSystem QubitSpace BK8Tensor
abbrev BK10Tensor := CompositeSystem QubitSpace BK9Tensor
abbrev BK11Tensor := CompositeSystem QubitSpace BK10Tensor
abbrev BK12Tensor := CompositeSystem QubitSpace BK11Tensor
abbrev BK13Tensor := CompositeSystem QubitSpace BK12Tensor
abbrev BK14Tensor := CompositeSystem QubitSpace BK13Tensor
abbrev BK15Tensor := CompositeSystem QubitSpace BK14Tensor
abbrev BK1BitTuple := Fin 2
abbrev BK2BitTuple := Fin 2 × BK1BitTuple
abbrev BK3BitTuple := Fin 2 × BK2BitTuple
abbrev BK4BitTuple := Fin 2 × BK3BitTuple
abbrev BK5BitTuple := Fin 2 × BK4BitTuple
abbrev BK6BitTuple := Fin 2 × BK5BitTuple
abbrev BK7BitTuple := Fin 2 × BK6BitTuple
abbrev BK8BitTuple := Fin 2 × BK7BitTuple
abbrev BK9BitTuple := Fin 2 × BK8BitTuple
abbrev BK10BitTuple := Fin 2 × BK9BitTuple
abbrev BK11BitTuple := Fin 2 × BK10BitTuple
abbrev BK12BitTuple := Fin 2 × BK11BitTuple
abbrev BK13BitTuple := Fin 2 × BK12BitTuple
abbrev BK14BitTuple := Fin 2 × BK13BitTuple
abbrev BK15BitTuple := Fin 2 × BK14BitTuple
abbrev BK15Register := QubitRegister (Fin 15)
def bk15TupleBitstring (bits : BK15BitTuple) : Bitstring (Fin 15) :=
  fun site =>
    match site.1 with
    | 0 => bits.1
    | 1 => bits.2.1
    | 2 => bits.2.2.1
    | 3 => bits.2.2.2.1
    | 4 => bits.2.2.2.2.1
    | 5 => bits.2.2.2.2.2.1
    | 6 => bits.2.2.2.2.2.2.1
    | 7 => bits.2.2.2.2.2.2.2.1
    | 8 => bits.2.2.2.2.2.2.2.2.1
    | 9 => bits.2.2.2.2.2.2.2.2.2.1
    | 10 => bits.2.2.2.2.2.2.2.2.2.2.1
    | 11 => bits.2.2.2.2.2.2.2.2.2.2.2.1
    | 12 => bits.2.2.2.2.2.2.2.2.2.2.2.2.1
    | 13 => bits.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    | _ => bits.2.2.2.2.2.2.2.2.2.2.2.2.2.2
def splitBK15Bitstring (bits : Bitstring (Fin 15)) : BK15BitTuple :=
  (bits 0, (bits 1, (bits 2, (bits 3, (bits 4, (bits 5, (bits 6,
    (bits 7, (bits 8, (bits 9, (bits 10, (bits 11, (bits 12,
      (bits 13, bits 14))))))))))))))
@[simp] theorem splitBK15Bitstring_bk15TupleBitstring (bits : BK15BitTuple) :
    splitBK15Bitstring (bk15TupleBitstring bits) = bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  rfl
@[simp] theorem bk15TupleBitstring_splitBK15Bitstring
    (bits : Bitstring (Fin 15)) :
    bk15TupleBitstring (splitBK15Bitstring bits) = bits := by
  funext site
  fin_cases site <;> rfl
def bk15BitstringEquiv : BK15BitTuple ≃ Bitstring (Fin 15) where
  toFun := bk15TupleBitstring
  invFun := splitBK15Bitstring
  left_inv := splitBK15Bitstring_bk15TupleBitstring
  right_inv := bk15TupleBitstring_splitBK15Bitstring
section
set_option maxRecDepth 65536
noncomputable def bk15TensorRegisterTransport :
    UnitaryTransport BK15Tensor BK15Register := by
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let sourceBasis := oneBasis.tensorProduct
    (oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct
            (oneBasis.tensorProduct
              (oneBasis.tensorProduct
                (oneBasis.tensorProduct
                  (oneBasis.tensorProduct
                    (oneBasis.tensorProduct
                      (oneBasis.tensorProduct
                        (oneBasis.tensorProduct
                          (oneBasis.tensorProduct
                            (oneBasis.tensorProduct oneBasis)))))))))))))
  let targetBasis := EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex
  let U := sourceBasis.equiv targetBasis bk15BitstringEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
end
theorem tensorDensity_convexCombination
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type w} {κ : Type*} [Fintype ι] [Fintype κ]
    (weight : ι → Real) (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1)
    (tailWeight : κ → Real) (sigma : κ → DensityOperator K)
    (htail_nonneg : ∀ j, 0 ≤ tailWeight j) (htail_sum : ∑ j, tailWeight j = 1) :
    DensityOperator.tensorDensity
        (DensityOperator.convexCombination Finset.univ weight rho
          (by intro i _; exact hweight_nonneg i) hweight_sum)
        (DensityOperator.convexCombination Finset.univ tailWeight sigma
          (by intro j _; exact htail_nonneg j) htail_sum) =
      DensityOperator.convexCombination Finset.univ
        (fun pair : ι × κ => weight pair.1 * tailWeight pair.2)
        (fun pair => DensityOperator.tensorDensity (rho pair.1) (sigma pair.2))
        (by
          intro pair _
          exact mul_nonneg (hweight_nonneg pair.1) (htail_nonneg pair.2))
        (by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, htail_sum, mul_one]
          exact hweight_sum) := by
  apply densityOperator_ext_toOperator
  simp only [DensityOperator.tensorDensity_toOperator,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  rw [DensityOperator.tensorMap_sum_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right]
  simp only [smul_smul, Complex.ofReal_mul]
  rw [DensityOperator.tensorDensity_toOperator]
structure FlatExpansion (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (ι : Type) [Fintype ι] where
  weight : ι → Real
  component : ι → DensityOperator H
  nonneg : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  physical : DensityOperator H
  physical_eq_flat : physical = DensityOperator.convexCombination Finset.univ
    weight component (by intro i _; exact nonneg i) sum_one
noncomputable def FlatExpansion.flat
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type} [Fintype ι]
    (expansion : FlatExpansion H ι) : DensityOperator H :=
  DensityOperator.convexCombination Finset.univ expansion.weight expansion.component
    (by intro i _; exact expansion.nonneg i) expansion.sum_one
noncomputable def aBasisFlatExpansion (epsilon : BK15Epsilon) :
    FlatExpansion QubitSpace (Fin 2) where
  weight := aInputWeight epsilon
  component := aInputComponent
  nonneg := aInputWeight_nonneg epsilon
  sum_one := sum_aInputWeight epsilon
  physical := diagonalAResource epsilon
  physical_eq_flat := rfl
noncomputable def prependABasisFlatExpansion {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (epsilon : BK15Epsilon)
    (tail : FlatExpansion K ι) :
    FlatExpansion (CompositeSystem QubitSpace K) (Fin 2 × ι) where
  weight := fun pair => aInputWeight epsilon pair.1 * tail.weight pair.2
  component := fun pair => DensityOperator.tensorDensity
    (aInputComponent pair.1) (tail.component pair.2)
  nonneg := by
    intro pair
    exact mul_nonneg (aInputWeight_nonneg epsilon pair.1) (tail.nonneg pair.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, tail.sum_one, mul_one]
    exact sum_aInputWeight epsilon
  physical := DensityOperator.tensorDensity (diagonalAResource epsilon) tail.physical
  physical_eq_flat := by
    calc
      DensityOperator.tensorDensity (diagonalAResource epsilon) tail.physical =
          DensityOperator.tensorDensity (diagonalAResource epsilon) tail.flat := by
            unfold FlatExpansion.flat
            exact congrArg (DensityOperator.tensorDensity (diagonalAResource epsilon))
              tail.physical_eq_flat
      _ = _ := tensorDensity_convexCombination
        (aInputWeight epsilon) aInputComponent (aInputWeight_nonneg epsilon)
        (sum_aInputWeight epsilon) tail.weight tail.component tail.nonneg tail.sum_one
noncomputable def bk15FlatExpansion (epsilon : BK15Epsilon) :
    FlatExpansion BK15Tensor BK15BitTuple := by
  let m1 := aBasisFlatExpansion epsilon
  let m2 := prependABasisFlatExpansion epsilon m1
  let m3 := prependABasisFlatExpansion epsilon m2
  let m4 := prependABasisFlatExpansion epsilon m3
  let m5 := prependABasisFlatExpansion epsilon m4
  let m6 := prependABasisFlatExpansion epsilon m5
  let m7 := prependABasisFlatExpansion epsilon m6
  let m8 := prependABasisFlatExpansion epsilon m7
  let m9 := prependABasisFlatExpansion epsilon m8
  let m10 := prependABasisFlatExpansion epsilon m9
  let m11 := prependABasisFlatExpansion epsilon m10
  let m12 := prependABasisFlatExpansion epsilon m11
  let m13 := prependABasisFlatExpansion epsilon m12
  let m14 := prependABasisFlatExpansion epsilon m13
  exact prependABasisFlatExpansion epsilon m14
noncomputable def bk15TensorDensity
    (inputs : ResourceInput 15 QubitSpace) : DensityOperator BK15Tensor :=
  DensityOperator.tensorDensity (inputs 0)
    (DensityOperator.tensorDensity (inputs 1)
      (DensityOperator.tensorDensity (inputs 2)
        (DensityOperator.tensorDensity (inputs 3)
          (DensityOperator.tensorDensity (inputs 4)
            (DensityOperator.tensorDensity (inputs 5)
              (DensityOperator.tensorDensity (inputs 6)
                (DensityOperator.tensorDensity (inputs 7)
                  (DensityOperator.tensorDensity (inputs 8)
                    (DensityOperator.tensorDensity (inputs 9)
                      (DensityOperator.tensorDensity (inputs 10)
                        (DensityOperator.tensorDensity (inputs 11)
                          (DensityOperator.tensorDensity (inputs 12)
                            (DensityOperator.tensorDensity (inputs 13)
                              (inputs 14))))))))))))))
noncomputable def bk15PrepareInput
    (inputs : ResourceInput 15 QubitSpace) : DensityOperator BK15Register :=
  bk15TensorRegisterTransport.conjDensity (bk15TensorDensity inputs)
noncomputable def bk15NoisyResources (epsilon : BK15Epsilon) :
    ResourceInput 15 QubitSpace :=
  fun _ => diagonalAResource epsilon
@[simp] theorem bk15PrepareInput_noisyResources (epsilon : BK15Epsilon) :
    bk15PrepareInput (bk15NoisyResources epsilon) =
      bk15TensorRegisterTransport.conjDensity
        (bk15TensorDensity (bk15NoisyResources epsilon)) :=
  rfl
def bk15WordWeight (epsilon : BK15Epsilon) (word : Word) : Real :=
  ∏ site : Fin 15, aInputWeight epsilon (word site)
theorem bk15WordWeight_nonneg (epsilon : BK15Epsilon) (word : Word) :
    0 ≤ bk15WordWeight epsilon word := by
  unfold bk15WordWeight
  exact Finset.prod_nonneg fun site _ => aInputWeight_nonneg epsilon (word site)
theorem sum_bk15WordWeight (epsilon : BK15Epsilon) :
    ∑ word : Word, bk15WordWeight epsilon word = 1 := by
  classical
  calc
    _ = ∑ word : Fin 15 → Fin 2,
        ∏ site : Fin 15, aInputWeight epsilon (word site) := by
      apply Fintype.sum_equiv (Equiv.refl (Fin 15 → Fin 2))
      intro word
      rfl
    _ = ∏ _site : Fin 15, ∑ bit : Fin 2, aInputWeight epsilon bit :=
      (Fintype.prod_sum (fun (_site : Fin 15) (bit : Fin 2) =>
        aInputWeight epsilon bit)).symm
    _ = 1 := by simp only [sum_aInputWeight, Finset.prod_const_one]
noncomputable def bk15WordResources (word : Word) : ResourceInput 15 QubitSpace :=
  fun site => aInputComponent (word site)
noncomputable def bk15ErrorWordDensity (word : Word) :
    DensityOperator BK15Register :=
  bk15PrepareInput (bk15WordResources word)
noncomputable def bk15FlatErrorWordMixture (epsilon : BK15Epsilon) :
    DensityOperator BK15Register :=
  DensityOperator.convexCombination Finset.univ (bk15WordWeight epsilon)
    bk15ErrorWordDensity
    (by
      intro word _
      exact bk15WordWeight_nonneg epsilon word)
    (sum_bk15WordWeight epsilon)
noncomputable def bk15ErrorWordMixture (epsilon : BK15Epsilon) :
    DensityOperator BK15Register :=
  bk15FlatErrorWordMixture epsilon
end NoisyInput
end BK15
end Distillation
end QEC


