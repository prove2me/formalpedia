-- Prove2me | Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
-- name    : QEC_Distillation_FifteenQubitH_Protocol
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T02:03:53.0596+00:00
-- url     : https://prove2.me/theorems/a8f9a8a4-b98a-4678-8777-1a5ac89ca0a9
-- title:
--   Protocol
-- statement:
--   Definitions and structural lemmas for Protocol, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Protocol.lean

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aBasisProjector_isSymmetricProjection
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_aZeroDensity_eq_phaseStateDensity
import Theorems.Thm_QEC_Distillation_BK15_NoisyInput_bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_le_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_one
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
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
namespace Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite
def aInputState : Fin 2 → QubitSpace
  | 0 => aZeroState
  | 1 => aOneState
@[simp] theorem aInputState_norm (bit : Fin 2) : ‖aInputState bit‖ = 1 := by
  fin_cases bit
  · exact aZeroState_norm
  · exact aOneState_norm
theorem aInputComponent_toOperator_rankOne (bit : Fin 2) :
    (aInputComponent bit).toOperator =
      (InnerProductSpace.rankOne Complex (aInputState bit) (aInputState bit)).toLinearMap := by
  fin_cases bit
  · change aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap
    rw [aZeroDensity_eq_phaseStateDensity,
      OneQubitMagic.phaseStateDensity_toOperator]
    rfl
  · change aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap
    rw [aOneDensity, UnitaryTransport.conjDensity_toOperator,
      aZeroDensity_eq_phaseStateDensity,
      OneQubitMagic.phaseStateDensity_toOperator,
      QuditSubsystem.conjOperator_rankOne]
    rfl
noncomputable def aInputBasis : OrthonormalBasis (Fin 2) Complex QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    aBasisTransport.toLinearIsometryEquiv
@[simp] theorem aInputBasis_apply (bit : Fin 2) :
    aInputBasis bit = aInputState bit := by
  fin_cases bit
  · change aBasisTransport
      (EuclideanSpace.basisFun (Fin 2) Complex 0) = aZeroState
    exact aBasisTransport_basis_zero
  · change aBasisTransport
      (EuclideanSpace.basisFun (Fin 2) Complex 1) = aOneState
    exact aBasisTransport_basis_one
noncomputable def wordBits (word : Word) : Bitstring (Fin 15) :=
  (bitstringWordEquiv (Fin 15)).symm word
@[simp] theorem wordBits_toWord (word : Word) :
    bitstringWordEquiv (Fin 15) (wordBits word) = word :=
  (bitstringWordEquiv (Fin 15)).apply_symm_apply word
@[simp] theorem wordBits_apply_cast (word : Word) (site : Fin 15) :
    ((wordBits word site : Fin 2) : ZMod 2) = word site := by
  have h := congrFun (wordBits_toWord word) site
  exact h
@[simp] theorem wordBits_apply (word : Word) (site : Fin 15) :
    wordBits word site = word site := by
  change (if word site = 0 then 0 else 1) = word site
  generalize hbit : word site = bit
  fin_cases bit <;> rfl
noncomputable def bk15TensorErrorState (word : Word) : BK15Tensor :=
  aInputState (wordBits word 0) ⊗ₜ[Complex]
    (aInputState (wordBits word 1) ⊗ₜ[Complex]
      (aInputState (wordBits word 2) ⊗ₜ[Complex]
        (aInputState (wordBits word 3) ⊗ₜ[Complex]
          (aInputState (wordBits word 4) ⊗ₜ[Complex]
            (aInputState (wordBits word 5) ⊗ₜ[Complex]
              (aInputState (wordBits word 6) ⊗ₜ[Complex]
                (aInputState (wordBits word 7) ⊗ₜ[Complex]
                  (aInputState (wordBits word 8) ⊗ₜ[Complex]
                    (aInputState (wordBits word 9) ⊗ₜ[Complex]
                      (aInputState (wordBits word 10) ⊗ₜ[Complex]
                        (aInputState (wordBits word 11) ⊗ₜ[Complex]
                          (aInputState (wordBits word 12) ⊗ₜ[Complex]
                            (aInputState (wordBits word 13) ⊗ₜ[Complex]
                              aInputState (wordBits word 14))))))))))))))
noncomputable def bk15ErrorWordState (word : Word) : BK15Register :=
  bk15TensorRegisterTransport (bk15TensorErrorState word)
set_option maxRecDepth 65536 in
/-- The right-associated tensor product of the fifteen one-qubit A bases. -/
noncomputable def bk15TensorAInputBasis :
    OrthonormalBasis BK15BitTuple Complex BK15Tensor :=
  aInputBasis.tensorProduct
    (aInputBasis.tensorProduct
      (aInputBasis.tensorProduct
        (aInputBasis.tensorProduct
          (aInputBasis.tensorProduct
            (aInputBasis.tensorProduct
              (aInputBasis.tensorProduct
                (aInputBasis.tensorProduct
                  (aInputBasis.tensorProduct
                    (aInputBasis.tensorProduct
                      (aInputBasis.tensorProduct
                        (aInputBasis.tensorProduct
                          (aInputBasis.tensorProduct
                            (aInputBasis.tensorProduct aInputBasis)))))))))))))
noncomputable def bk15AErrorBasis : OrthonormalBasis Word Complex BK15Register :=
  ((bk15TensorAInputBasis.map
      bk15TensorRegisterTransport.toLinearIsometryEquiv).reindex
    (bk15BitstringEquiv.trans (bitstringWordEquiv (Fin 15))))
set_option maxRecDepth 65536 in
@[simp] theorem bk15AErrorBasis_apply (word : Word) :
    bk15AErrorBasis word = bk15ErrorWordState word := by
  rw [bk15AErrorBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
  change bk15TensorRegisterTransport
      (bk15TensorAInputBasis
        (splitBK15Bitstring (wordBits word))) =
    bk15TensorRegisterTransport (bk15TensorErrorState word)
  congr 1
  simp only [bk15TensorAInputBasis, bk15TensorErrorState, splitBK15Bitstring,
    OrthonormalBasis.tensorProduct_apply', aInputBasis_apply]
set_option maxRecDepth 65536 in
/-- The previously constructed physical error-word density is exactly the
rank-one projector on the corresponding member of the A-error basis. -/
theorem bk15ErrorWordDensity_toOperator_rankOne (word : Word) :
    (bk15ErrorWordDensity word).toOperator =
      (InnerProductSpace.rankOne Complex
        (bk15ErrorWordState word) (bk15ErrorWordState word)).toLinearMap := by
  have hcomponent (bit : Bit) :
      (aInputComponent bit).toOperator =
        (InnerProductSpace.rankOne Complex (aInputState bit) (aInputState bit)).toLinearMap :=
    aInputComponent_toOperator_rankOne bit
  unfold bk15ErrorWordDensity bk15PrepareInput bk15TensorDensity bk15WordResources
  simp only [UnitaryTransport.conjDensity_toOperator,
    DensityOperator.tensorDensity_toOperator,
    hcomponent, DensityOperator.tensorMap_rankOne]
  rw [QuditSubsystem.conjOperator_rankOne]
  simp only [bk15ErrorWordState, bk15TensorErrorState, wordBits_apply]
abbrev ZCheckIndex := Sum (Fin 4) QuadraticIndex
abbrev XCheckIndex := Fin 4
abbrev ZJointSyndrome := JointSyndrome ZCheckIndex
abbrev XJointSyndrome := JointSyndrome XCheckIndex
def signToBit : StabilizerOutcome -> Bit
  | .positive => 0
  | .negative => 1
def bitToSign (bit : Bit) : StabilizerOutcome :=
  if bit = 0 then .positive else .negative
@[simp] theorem signToBit_bitToSign (bit : Bit) : signToBit (bitToSign bit) = bit := by
  fin_cases bit <;> rfl
@[simp] theorem bitToSign_signToBit (sign : StabilizerOutcome) :
    bitToSign (signToBit sign) = sign := by
  cases sign <;> rfl
def binarySyndrome {Index : Type} (outcome : JointSyndrome Index) : Index -> Bit :=
  fun check => signToBit (outcome check)
def signSyndrome {Index : Type} (syndrome : Index -> Bit) : JointSyndrome Index :=
  fun check => bitToSign (syndrome check)
@[simp] theorem binarySyndrome_signSyndrome {Index : Type}
    (syndrome : Index -> Bit) : binarySyndrome (signSyndrome syndrome) = syndrome := by
  funext check
  exact signToBit_bitToSign (syndrome check)
@[simp] theorem signSyndrome_binarySyndrome {Index : Type}
    (outcome : JointSyndrome Index) : signSyndrome (binarySyndrome outcome) = outcome := by
  funext check
  exact bitToSign_signToBit (outcome check)
abbrev zBinarySyndrome (outcome : ZJointSyndrome) : ZCheckIndex -> Bit :=
  binarySyndrome outcome
abbrev xBinarySyndrome (outcome : XJointSyndrome) : XCheckIndex -> Bit :=
  binarySyndrome outcome
private def syndromeBasisWord (g : ZCheckIndex) : Word := fun site =>
  let mask : Nat := match g with
  | Sum.inl j => (![128, 8, 2, 1] : Fin 4 → Nat) j
  | Sum.inr ij =>
      if ij.1.1 = 0 then (if ij.1.2 = 1 then 2184 else if ij.1.2 = 2 then 642 else 385)
      else if ij.1.1 = 1 then (if ij.1.2 = 2 then 42 else 25)
      else 7
  if mask.testBit site.val then 1 else 0
private theorem syndrome_basis_0 : l2Syndrome (syndromeBasisWord ((Sum.inl 0) : ZCheckIndex)) = Pi.single ((Sum.inl 0) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_1 : l2Syndrome (syndromeBasisWord ((Sum.inl 1) : ZCheckIndex)) = Pi.single ((Sum.inl 1) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_2 : l2Syndrome (syndromeBasisWord ((Sum.inl 2) : ZCheckIndex)) = Pi.single ((Sum.inl 2) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_3 : l2Syndrome (syndromeBasisWord ((Sum.inl 3) : ZCheckIndex)) = Pi.single ((Sum.inl 3) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_4 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(0, 1), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(0, 1), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_5 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(0, 2), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(0, 2), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_6 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(0, 3), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(0, 3), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_7 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(1, 2), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(1, 2), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_8 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(1, 3), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(1, 3), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_9 : l2Syndrome (syndromeBasisWord ((Sum.inr ⟨(2, 3), by decide⟩) : ZCheckIndex)) = Pi.single ((Sum.inr ⟨(2, 3), by decide⟩) : ZCheckIndex) 1 := by
  decide +kernel
private theorem syndrome_basis_image (g : ZCheckIndex) : l2Syndrome (syndromeBasisWord g) = Pi.single g 1 := by
  fin_cases g
  · exact syndrome_basis_0
  · exact syndrome_basis_1
  · exact syndrome_basis_2
  · exact syndrome_basis_3
  · exact syndrome_basis_4
  · exact syndrome_basis_5
  · exact syndrome_basis_6
  · exact syndrome_basis_7
  · exact syndrome_basis_8
  · exact syndrome_basis_9
theorem l2Syndrome_surjective : Function.Surjective l2Syndrome := by
  intro syndrome
  refine ⟨∑ g, syndrome g • syndromeBasisWord g, ?_⟩
  rw [map_sum]
  simp only [map_smul, syndrome_basis_image]
  funext g
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
noncomputable def l2SyndromeSection (syndrome : ZCheckIndex -> Bit) : Word :=
  if syndrome = 0 then 0 else Classical.choose (l2Syndrome_surjective syndrome)
@[simp] theorem l2SyndromeSection_zero :
    l2SyndromeSection (0 : ZCheckIndex -> Bit) = 0 := by
  simp [l2SyndromeSection]
@[simp] theorem l2SyndromeSection_apply (syndrome : ZCheckIndex -> Bit) :
    l2Syndrome (l2SyndromeSection syndrome) = syndrome :=
  by
    by_cases hsyndrome : syndrome = 0
    · subst syndrome
      simp [l2SyndromeSection, l2Syndrome]
      rfl
    · simpa [l2SyndromeSection, hsyndrome] using
        Classical.choose_spec (l2Syndrome_surjective syndrome)
def oneSiteWord (site : Fin 15) : Word := Pi.single site 1
theorem oneSiteWord_l1Syndrome_ne_zero (site : Fin 15) :
    l1Syndrome (oneSiteWord site) ≠ 0 := by
  decide +kernel +revert
def zChecks (check : ZCheckIndex) : Binary (Fin 15) :=
  cssZCheck (l2Generator check)
def xChecks (check : XCheckIndex) : Binary (Fin 15) :=
  cssXCheck (linearGenerator check)
theorem zChecks_commute (left right : ZCheckIndex) :
    Commutes (zChecks left) (zChecks right) :=
  cssZCheck_commutes_cssZCheck _ _
theorem xChecks_commute (left right : XCheckIndex) :
    Commutes (xChecks left) (xChecks right) :=
  cssXCheck_commutes_cssXCheck _ _
def zProjector (outcome : ZJointSyndrome) : Operator BK15Register :=
  jointStabilizerProjector zChecks zChecks_commute outcome
def xProjector (outcome : XJointSyndrome) : Operator BK15Register :=
  jointStabilizerProjector xChecks xChecks_commute outcome
@[simp] theorem zProjector_adjoint (outcome : ZJointSyndrome) :
    LinearMap.adjoint (zProjector outcome) = zProjector outcome :=
  jointStabilizerProjector_adjoint zChecks zChecks_commute outcome
@[simp] theorem xProjector_adjoint (outcome : XJointSyndrome) :
    LinearMap.adjoint (xProjector outcome) = xProjector outcome :=
  jointStabilizerProjector_adjoint xChecks xChecks_commute outcome
@[simp] theorem zProjector_idempotent (outcome : ZJointSyndrome) :
    zProjector outcome * zProjector outcome = zProjector outcome :=
  jointStabilizerProjector_idempotent zChecks zChecks_commute outcome
@[simp] theorem xProjector_idempotent (outcome : XJointSyndrome) :
    xProjector outcome * xProjector outcome = xProjector outcome :=
  jointStabilizerProjector_idempotent xChecks xChecks_commute outcome
theorem sum_zProjector_eq_one :
    ∑ outcome : ZJointSyndrome, zProjector outcome = 1 :=
  sum_jointStabilizerProjector_eq_one zChecks zChecks_commute
theorem sum_xProjector_eq_one :
    ∑ outcome : XJointSyndrome, xProjector outcome = 1 :=
  sum_jointStabilizerProjector_eq_one xChecks xChecks_commute
noncomputable def aObservableTransport : UnitaryTransport QubitSpace QubitSpace :=
  aBasisTransport.symm.trans (zTransport.trans aBasisTransport)
noncomputable def aBitTransport (bit : Bit) : UnitaryTransport QubitSpace QubitSpace :=
  if bit = 0 then UnitaryTransport.identity QubitSpace else aObservableTransport
noncomputable def aBitBasis (bit : Bit) : OrthonormalBasis (Fin 2) Complex QubitSpace :=
  (EuclideanSpace.basisFun (Fin 2) Complex).map
    (aBitTransport bit).toLinearIsometryEquiv
@[simp] theorem aBitTransport_aInputState (word error : Bit) :
    aBitTransport word (aInputState error) =
      binaryPhaseScalar (word * error) • aInputState error := by
  fin_cases word <;> fin_cases error <;>
    simp only [aInputState, aOneState_eq_pauliZ]
  · change (UnitaryTransport.identity QubitSpace) aZeroState =
      (1 : Complex) • aZeroState
    simp
  · change (UnitaryTransport.identity QubitSpace) aOneState =
      (1 : Complex) • aOneState
    simp
  · change aObservableTransport aZeroState = (1 : Complex) • aZeroState
    change aBasisObservable aZeroState = _
    simp
  · change aObservableTransport aOneState = (-1 : Complex) • aOneState
    change aBasisObservable aOneState = _
    simpa using aBasisObservable_aOneState
set_option maxRecDepth 65536 in
/-- The actual tensor-product correction `A(word)` before transport to Fin-15. -/
noncomputable def aWordCorrectionTensor (word : Word) :
    UnitaryTransport BK15Tensor BK15Tensor := by
  let U14 : BK1Tensor ≃ₗᵢ[Complex] BK1Tensor :=
    (aBitTransport (word 14)).toLinearIsometryEquiv
  let U13 : BK2Tensor ≃ₗᵢ[Complex] BK2Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 13)).toLinearIsometryEquiv U14
  let U12 : BK3Tensor ≃ₗᵢ[Complex] BK3Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 12)).toLinearIsometryEquiv U13
  let U11 : BK4Tensor ≃ₗᵢ[Complex] BK4Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 11)).toLinearIsometryEquiv U12
  let U10 : BK5Tensor ≃ₗᵢ[Complex] BK5Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 10)).toLinearIsometryEquiv U11
  let U9 : BK6Tensor ≃ₗᵢ[Complex] BK6Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 9)).toLinearIsometryEquiv U10
  let U8 : BK7Tensor ≃ₗᵢ[Complex] BK7Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 8)).toLinearIsometryEquiv U9
  let U7 : BK8Tensor ≃ₗᵢ[Complex] BK8Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 7)).toLinearIsometryEquiv U8
  let U6 : BK9Tensor ≃ₗᵢ[Complex] BK9Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 6)).toLinearIsometryEquiv U7
  let U5 : BK10Tensor ≃ₗᵢ[Complex] BK10Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 5)).toLinearIsometryEquiv U6
  let U4 : BK11Tensor ≃ₗᵢ[Complex] BK11Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 4)).toLinearIsometryEquiv U5
  let U3 : BK12Tensor ≃ₗᵢ[Complex] BK12Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 3)).toLinearIsometryEquiv U4
  let U2 : BK13Tensor ≃ₗᵢ[Complex] BK13Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 2)).toLinearIsometryEquiv U3
  let U1 : BK14Tensor ≃ₗᵢ[Complex] BK14Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 1)).toLinearIsometryEquiv U2
  let U0 : BK15Tensor ≃ₗᵢ[Complex] BK15Tensor :=
    TensorProduct.congrIsometry
      (aBitTransport (word 0)).toLinearIsometryEquiv U1
  exact { toLinearEquiv := U0.toLinearEquiv, map_inner := U0.inner_map_map }
noncomputable def aWordCorrectionTransport (word : Word) :
    UnitaryTransport BK15Register BK15Register :=
  bk15TensorRegisterTransport.symm.trans
    ((aWordCorrectionTensor word).trans bk15TensorRegisterTransport)
set_option maxRecDepth 65536 in
@[simp] theorem aWordCorrectionTransport_zero_apply (psi : BK15Register) :
    aWordCorrectionTransport (0 : Word) psi = psi := by
  change bk15TensorRegisterTransport
      (aWordCorrectionTensor 0
        (bk15TensorRegisterTransport.toLinearEquiv.symm psi)) = psi
  simp [aWordCorrectionTensor, aBitTransport, UnitaryTransport.identity]
set_option maxRecDepth 65536 in
noncomputable def bk15TensorComputationalBasis :
    OrthonormalBasis BK15BitTuple Complex BK15Tensor :=
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  oneBasis.tensorProduct
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
set_option maxRecDepth 65536 in
noncomputable def tensor15Vector
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : QubitSpace) :
    BK15Tensor :=
  v0 ⊗ₜ[Complex]
    (v1 ⊗ₜ[Complex]
      (v2 ⊗ₜ[Complex]
        (v3 ⊗ₜ[Complex]
          (v4 ⊗ₜ[Complex]
            (v5 ⊗ₜ[Complex]
              (v6 ⊗ₜ[Complex]
                (v7 ⊗ₜ[Complex]
                  (v8 ⊗ₜ[Complex]
                    (v9 ⊗ₜ[Complex]
                      (v10 ⊗ₜ[Complex]
                        (v11 ⊗ₜ[Complex]
                          (v12 ⊗ₜ[Complex]
                            (v13 ⊗ₜ[Complex] v14)))))))))))))
set_option maxRecDepth 65536 in
@[simp] theorem bk15TensorComputationalBasis_apply
    (bits : BK15BitTuple) :
    bk15TensorComputationalBasis bits =
      tensor15Vector
        (EuclideanSpace.basisFun (Fin 2) Complex bits.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (EuclideanSpace.basisFun (Fin 2) Complex bits.2.2.2.2.2.2.2.2.2.2.2.2.2.2) := by
  simp only [bk15TensorComputationalBasis,
    OrthonormalBasis.tensorProduct_apply', tensor15Vector]
set_option maxRecDepth 65536 in
@[simp] theorem bk15TensorRegisterTransport_apply_computationalBasis
    (bits : BK15BitTuple) :
    bk15TensorRegisterTransport (bk15TensorComputationalBasis bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex
        (bk15TupleBitstring bits) := by
  dsimp [bk15TensorRegisterTransport, bk15TensorComputationalBasis]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
noncomputable def bk15TensorErrorVector
    (error : Word) : BK15Tensor :=
  tensor15Vector
    (aInputState (wordBits error 0))
    (aInputState (wordBits error 1))
    (aInputState (wordBits error 2))
    (aInputState (wordBits error 3))
    (aInputState (wordBits error 4))
    (aInputState (wordBits error 5))
    (aInputState (wordBits error 6))
    (aInputState (wordBits error 7))
    (aInputState (wordBits error 8))
    (aInputState (wordBits error 9))
    (aInputState (wordBits error 10))
    (aInputState (wordBits error 11))
    (aInputState (wordBits error 12))
    (aInputState (wordBits error 13))
    (aInputState (wordBits error 14))
def fin15Nested (f : Fin 15 → Complex) : Complex :=
    f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 *
      (f 7 * (f 8 * (f 9 * (f 10 * (f 11 * (f 12 *
        (f 13 * f 14)))))))))))))
def finBitToBit (bit : Fin 2) : Bit :=
  if bit = 0 then 0 else 1
@[simp] theorem binaryPhaseScalar_mul_self (bit : ZMod 2) :
    binaryPhaseScalar bit * binaryPhaseScalar bit = 1 := by
  rw [← binaryPhaseScalar_add]
  have h : bit + bit = 0 := by
    fin_cases bit <;> decide
  rw [h, binaryPhaseScalar_zero]
abbrev History := ZJointSyndrome × XJointSyndrome
def historyOutcome (history : History) : DistillationOutcome :=
  if xBinarySyndrome history.2 = 0 then .accepted else .rejected
noncomputable def historyCorrection (outcome : ZJointSyndrome) :
    UnitaryTransport BK15Register BK15Register :=
  aWordCorrectionTransport (l2SyndromeSection (zBinarySyndrome outcome))
@[simp] theorem binaryPhaseScalar_signToBit
    (outcome : StabilizerOutcome) :
    binaryPhaseScalar (signToBit outcome) = outcome.sign := by
  cases outcome <;> norm_num [signToBit, binaryPhaseScalar,
    StabilizerOutcome.sign]
noncomputable def historyKraus (history : History) : Operator BK15Register :=
  xProjector history.2 *
    (historyCorrection history.1).symm.toLinearEquiv.toLinearMap *
    zProjector history.1
noncomputable def historyKrausFamily :
    FiniteKrausFamily History BK15Register BK15Register where
  operator := historyKraus
theorem historyCorrection_comp_symm (outcome : ZJointSyndrome) :
    (historyCorrection outcome).toLinearEquiv.toLinearMap *
      (historyCorrection outcome).symm.toLinearEquiv.toLinearMap = 1 := by
  ext psi
  simp [Module.End.mul_apply, UnitaryTransport.symm]
theorem adjoint_comp_projective_history
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (Z X : Operator H) (U : UnitaryTransport H H)
    (hZ : LinearMap.adjoint Z = Z) (hX : LinearMap.adjoint X = X) :
    (LinearMap.adjoint (X * U.symm.toLinearEquiv.toLinearMap * Z)).comp
        (X * U.symm.toLinearEquiv.toLinearMap * Z) =
      Z * U.toLinearEquiv.toLinearMap * X * X *
        U.symm.toLinearEquiv.toLinearMap * Z := by
  have hU : LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap =
      U.toLinearEquiv.toLinearMap := by
    change LinearMap.adjoint U.toLinearEquiv.symm.toLinearMap = _
    exact U.adjoint_symm_toLinearMap
  simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hZ, hX, hU,
    LinearMap.comp_assoc]
theorem historyKraus_adjoint_comp
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome) :
    (LinearMap.adjoint (historyKraus (zOutcome, xOutcome))).comp
        (historyKraus (zOutcome, xOutcome)) =
      zProjector zOutcome *
        (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
        xProjector xOutcome * xProjector xOutcome *
        (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
      zProjector zOutcome := by
  simpa only [historyKraus] using
    adjoint_comp_projective_history
      (zProjector zOutcome) (xProjector xOutcome) (historyCorrection zOutcome)
      (zProjector_adjoint zOutcome) (xProjector_adjoint xOutcome)
theorem historyKrausFamily_complete : historyKrausFamily.Complete := by
  classical
  rw [FiniteKrausFamily.Complete, Fintype.sum_prod_type]
  calc
    (∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (LinearMap.adjoint (historyKrausFamily.operator (zOutcome, xOutcome))).comp
          (historyKrausFamily.operator (zOutcome, xOutcome))) =
        ∑ zOutcome : ZJointSyndrome, zProjector zOutcome := by
      apply Finset.sum_congr rfl
      intro zOutcome _
      simp only [historyKrausFamily, historyKraus_adjoint_comp]
      calc
        (∑ xOutcome : XJointSyndrome,
            zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              xProjector xOutcome * xProjector xOutcome *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome) =
            zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              (∑ xOutcome : XJointSyndrome,
                xProjector xOutcome * xProjector xOutcome) *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome := by
                simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = zProjector zOutcome *
              (historyCorrection zOutcome).toLinearEquiv.toLinearMap *
              (∑ xOutcome : XJointSyndrome, xProjector xOutcome) *
              (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
              zProjector zOutcome := by
                congr 3
                apply Finset.sum_congr rfl
                intro xOutcome _
                exact xProjector_idempotent xOutcome
        _ = zProjector zOutcome := by
          rw [show (∑ xOutcome : XJointSyndrome, xProjector xOutcome) = 1 by
            exact sum_xProjector_eq_one]
          calc
            zProjector zOutcome *
                (historyCorrection zOutcome).toLinearEquiv.toLinearMap * 1 *
                (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap *
                zProjector zOutcome =
              zProjector zOutcome *
                ((historyCorrection zOutcome).toLinearEquiv.toLinearMap *
                  (historyCorrection zOutcome).symm.toLinearEquiv.toLinearMap) *
                zProjector zOutcome := by simp only [mul_one, mul_assoc]
            _ = zProjector zOutcome * zProjector zOutcome := by
              rw [historyCorrection_comp_symm]
              simp
            _ = zProjector zOutcome :=
              zProjector_idempotent zOutcome
    _ = 1 := sum_zProjector_eq_one
noncomputable def historyInstrument :
    FiniteInstrument History DistillationOutcome BK15Register BK15Register where
  kraus := historyKrausFamily
  observe := historyOutcome
theorem historyInstrument_complete : historyInstrument.kraus.Complete := by
  change historyKrausFamily.Complete
  exact historyKrausFamily_complete
noncomputable def rawInput (epsilon : BK15Epsilon) : DensityOperator BK15Register :=
  bk15ErrorWordMixture epsilon
noncomputable def rawEndpoint (epsilon : BK15Epsilon) (outcome : DistillationOutcome) :
    Operator BK15Register :=
  historyInstrument.branchOperator outcome (rawInput epsilon).toOperator
noncomputable def endpointWeight (epsilon : BK15Epsilon) (outcome : DistillationOutcome) : Real :=
  historyInstrument.bornWeight outcome (rawInput epsilon)
noncomputable def historyChannel : QuantumChannel BK15Register BK15Register :=
  historyInstrument.kraus.toQuantumChannel historyInstrument_complete
theorem endpointWeight_nonneg (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) : 0 ≤ endpointWeight epsilon outcome :=
  historyInstrument.bornWeight_nonneg outcome (rawInput epsilon)
theorem endpointWeights_sum (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted + endpointWeight epsilon .rejected = 1 := by
  have h := historyInstrument.sum_bornWeight_eq_one
    historyInstrument_complete (rawInput epsilon)
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {.accepted, .rejected} by decide] at h
  simpa [endpointWeight] using h
set_option maxRecDepth 65536 in
@[simp] theorem rawEndpoint_eq_branchOperator (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) :
    rawEndpoint epsilon outcome =
      historyInstrument.branchOperator outcome (rawInput epsilon).toOperator :=
  rfl
theorem historyBranchOperators_reconstruct (epsilon : BK15Epsilon) :
    historyInstrument.branchOperator .accepted (rawInput epsilon).toOperator +
        historyInstrument.branchOperator .rejected (rawInput epsilon).toOperator =
      ((historyInstrument.kraus.toQuantumChannel historyInstrument_complete).mapDensity
        (rawInput epsilon)).toOperator := by
  have h := historyInstrument.sum_branchOperator_eq_mapDensity_toOperator
    historyInstrument_complete (rawInput epsilon)
  rw [show (Finset.univ : Finset DistillationOutcome) =
    {.accepted, .rejected} by decide] at h
  simpa only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_singleton] using h
theorem rawEndpoints_reconstruct (epsilon : BK15Epsilon) :
    rawEndpoint epsilon .accepted + rawEndpoint epsilon .rejected =
      ((historyInstrument.kraus.toQuantumChannel historyInstrument_complete).mapDensity
        (rawInput epsilon)).toOperator := by
  rw [rawEndpoint_eq_branchOperator, rawEndpoint_eq_branchOperator]
  exact historyBranchOperators_reconstruct epsilon
def bk15CSSRows : Triorthogonal.BinaryRowFamily Unit (Fin 4) (Fin 15) where
  oddRow _ := allOnes
  evenRow := linearGenerator
theorem bk15CSSRows_triorthogonal : bk15CSSRows.IsTriorthogonal := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel +revert
abbrev LogicalRegister := QubitRegister Unit
noncomputable def bk15EncodedCode : EncodedCode LogicalRegister BK15Register :=
  bk15CSSRows.encodedCode bk15CSSRows_triorthogonal
def ambientEncodingIsometry : LogicalRegister →ₗᵢ[Complex] BK15Register :=
  bk15EncodedCode.code.carrier.subtypeₗᵢ.comp
    bk15EncodedCode.encoding.toLinearIsometry
@[simp] theorem ambientEncodingIsometry_apply (psi : LogicalRegister) :
    ambientEncodingIsometry psi = (bk15EncodedCode.encoding psi : BK15Register) :=
  rfl
def codeDecoderBranch : BK15Register →ₗ[Complex] LogicalRegister :=
  LinearMap.adjoint ambientEncodingIsometry.toLinearMap
@[simp] theorem codeDecoderBranch_encoded (psi : LogicalRegister) :
    codeDecoderBranch (ambientEncodingIsometry psi) = psi := by
  change LinearMap.adjoint ambientEncodingIsometry.toLinearMap
    (ambientEncodingIsometry.toLinearMap psi) = psi
  exact LinearMap.congr_fun ambientEncodingIsometry.adjoint_comp_self' psi
theorem adjoint_codeDecoderBranch : LinearMap.adjoint codeDecoderBranch =
    ambientEncodingIsometry.toLinearMap := by
  rw [codeDecoderBranch, LinearMap.adjoint_adjoint]
def decoderCodeProjector : Operator BK15Register :=
  (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch
@[simp] theorem decoderCodeProjector_encoded (psi : LogicalRegister) :
    decoderCodeProjector (ambientEncodingIsometry psi) = ambientEncodingIsometry psi := by
  change LinearMap.adjoint codeDecoderBranch
    (codeDecoderBranch (ambientEncodingIsometry psi)) = ambientEncodingIsometry psi
  rw [codeDecoderBranch_encoded, adjoint_codeDecoderBranch]
  rfl
theorem codeDecoderBranch_comp_adjoint :
    codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch) = 1 := by
  rw [adjoint_codeDecoderBranch, codeDecoderBranch]
  exact ambientEncodingIsometry.adjoint_comp_self'
theorem decoderCodeProjector_idempotent :
    decoderCodeProjector.comp decoderCodeProjector = decoderCodeProjector := by
  rw [decoderCodeProjector]
  calc
    ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch).comp
        ((LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch) =
      (LinearMap.adjoint codeDecoderBranch).comp
        ((codeDecoderBranch.comp (LinearMap.adjoint codeDecoderBranch)).comp
          codeDecoderBranch) := by
            ext psi
            rfl
    _ = (LinearMap.adjoint codeDecoderBranch).comp
          ((1 : Operator LogicalRegister).comp codeDecoderBranch) := by
            rw [codeDecoderBranch_comp_adjoint]
    _ = (LinearMap.adjoint codeDecoderBranch).comp codeDecoderBranch := by
      ext psi
      rfl
theorem decoderCodeProjector_adjoint :
    LinearMap.adjoint decoderCodeProjector = decoderCodeProjector := by
  simp [decoderCodeProjector, LinearMap.adjoint_comp]
def decoderComplementProjector : Operator BK15Register := 1 - decoderCodeProjector
theorem decoderComplementProjector_adjoint :
    LinearMap.adjoint decoderComplementProjector = decoderComplementProjector := by
  simp [decoderComplementProjector, decoderCodeProjector_adjoint]
theorem decoderComplementProjector_idempotent :
    decoderComplementProjector.comp decoderComplementProjector = decoderComplementProjector := by
  ext psi
  have hprojector := LinearMap.congr_fun decoderCodeProjector_idempotent psi
  simp only [decoderComplementProjector, LinearMap.comp_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_sub] at hprojector ⊢
  rw [hprojector]
  abel_nf
@[simp] theorem decoderComplementProjector_encoded (psi : LogicalRegister) :
    decoderComplementProjector (ambientEncodingIsometry psi) = 0 := by
  simp only [decoderComplementProjector, LinearMap.sub_apply, Module.End.one_apply]
  rw [decoderCodeProjector_encoded]
  abel_nf
noncomputable def decoderFallbackState : LogicalRegister :=
  EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => 0)
theorem decoderFallbackState_inner_self :
    inner Complex decoderFallbackState decoderFallbackState = 1 := by
  simp [decoderFallbackState]
theorem decoderFallbackState_normSq : ‖decoderFallbackState‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), decoderFallbackState_inner_self]
  norm_num
noncomputable def decoderPhysicalBasis :=
  stdOrthonormalBasis Complex BK15Register
def complementDecoderBranch
    (i : Fin (Module.finrank Complex BK15Register)) :
    BK15Register →ₗ[Complex] LogicalRegister :=
  (InnerProductSpace.rankOne Complex decoderFallbackState
    (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap
theorem complementDecoderBranch_adjoint_comp
    (i : Fin (Module.finrank Complex BK15Register)) :
    (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap := by
  have hadjoint : LinearMap.adjoint
      ((InnerProductSpace.rankOne Complex decoderFallbackState
        (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      (InnerProductSpace.rankOne Complex
        (decoderComplementProjector (decoderPhysicalBasis i))
        decoderFallbackState).toLinearMap := by
    rw [LinearMap.adjoint_eq_toCLM_adjoint]
    change ((InnerProductSpace.rankOne Complex decoderFallbackState
      (decoderComplementProjector (decoderPhysicalBasis i))).adjoint).toLinearMap = _
    rw [InnerProductSpace.adjoint_rankOne]
  apply LinearMap.ext
  intro psi
  simp only [complementDecoderBranch]
  rw [hadjoint]
  have hnormSq : (↑‖decoderFallbackState‖ : Complex) ^ 2 = 1 := by
    norm_cast
    exact decoderFallbackState_normSq
  simp [LinearMap.comp_apply, hnormSq]
theorem sum_complementDecoderBranch_adjoint_comp :
    ∑ i : Fin (Module.finrank Complex BK15Register),
      (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i) =
        decoderComplementProjector := by
  simp_rw [complementDecoderBranch_adjoint_comp]
  calc
    (∑ i, (InnerProductSpace.rankOne Complex
      (decoderComplementProjector (decoderPhysicalBasis i))
      (decoderComplementProjector (decoderPhysicalBasis i))).toLinearMap) =
      decoderComplementProjector.comp (LinearMap.adjoint decoderComplementProjector) := by
        apply LinearMap.ext
        intro psi
        simp only [LinearMap.sum_apply, LinearMap.comp_apply]
        rw [← decoderPhysicalBasis.sum_repr'
          (LinearMap.adjoint decoderComplementProjector psi)]
        simp only [map_sum, map_smul]
        apply Finset.sum_congr rfl
        intro i _
        rw [LinearMap.adjoint_inner_right]
        rfl
    _ = decoderComplementProjector.comp decoderComplementProjector := by
      rw [decoderComplementProjector_adjoint]
    _ = decoderComplementProjector := decoderComplementProjector_idempotent
def decoderKrausFamily :
    FiniteKrausFamily (Sum Unit (Fin (Module.finrank Complex BK15Register)))
      BK15Register LogicalRegister where
  operator
    | .inl _ => codeDecoderBranch
    | .inr i => complementDecoderBranch i
theorem decoderKrausFamily_complete : decoderKrausFamily.Complete := by
  rw [FiniteKrausFamily.Complete, Fintype.sum_sum_type]
  change (∑ _ : Unit, decoderCodeProjector) +
      (∑ i : Fin (Module.finrank Complex BK15Register),
        (LinearMap.adjoint (complementDecoderBranch i)).comp (complementDecoderBranch i)) = 1
  rw [Fintype.sum_unique, sum_complementDecoderBranch_adjoint_comp]
  simp [decoderComplementProjector]
noncomputable def decoderChannel : QuantumChannel BK15Register LogicalRegister :=
  decoderKrausFamily.toQuantumChannel decoderKrausFamily_complete
theorem sandwich_rankOne {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (L : H →ₗ[Complex] K) (psi : H) :
    L.comp ((InnerProductSpace.rankOne Complex psi psi).toLinearMap.comp
      (LinearMap.adjoint L)) =
      (InnerProductSpace.rankOne Complex (L psi) (L psi)).toLinearMap := by
  ext x
  simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    LinearMap.adjoint_inner_right]
noncomputable def cssWitnessState : BK15Register :=
  ambientEncodingIsometry decoderFallbackState
theorem cssWitnessState_ne_zero : cssWitnessState ≠ 0 := by
  intro hzero
  have hlogical : decoderFallbackState = 0 :=
    ambientEncodingIsometry.injective (by simpa [cssWitnessState] using hzero)
  have hinner := decoderFallbackState_inner_self
  rw [hlogical] at hinner
  simp at hinner
theorem cssWitness_fixed (P : Binary (Fin 15))
    (hP : P ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual) :
    toQubitOperator P cssWitnessState = cssWitnessState := by
  have hmem : cssWitnessState ∈ bk15EncodedCode.code.carrier := by
    change (bk15EncodedCode.encoding decoderFallbackState : BK15Register) ∈
      bk15EncodedCode.code.carrier
    exact (bk15EncodedCode.encoding decoderFallbackState).property
  exact (mem_binaryCSSQuantumCodeOfDualLe_carrier
    bk15CSSRows.evenCode bk15CSSRows.rowCode.dual
    bk15CSSRows.cssDualContainment cssWitnessState).1 hmem P hP
theorem cssWitness_xCheck_fixed (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check) cssWitnessState = cssWitnessState := by
  have hP : xChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inl ⟨linearGenerator check,
      bk15CSSRows.evenRow_mem_evenCode check, rfl⟩
  simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using cssWitness_fixed (xChecks check) hP
set_option maxHeartbeats 800000 in
theorem l2Generator_mem_cssRowCodeDual (check : ZCheckIndex) :
    l2Generator check ∈ bk15CSSRows.rowCode.dual.carrier := by
  rw [Coding.LinearCode.mem_dual]
  intro word hword
  change word ∈ Submodule.span (ZMod 2) (Set.range bk15CSSRows.row) at hword
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hword
  · intro generator hgenerator
    rcases hgenerator with ⟨tag, rfl⟩
    rcases tag with logical | stabilizer
    · cases logical
      decide +kernel +revert
    · decide +kernel +revert
  · simp
  · intro left right _hleft _hright hleft hright
    calc
      Coding.wordPairing (l2Generator check) (left + right) =
          Coding.wordPairing (l2Generator check) left +
            Coding.wordPairing (l2Generator check) right := by
              exact map_add (Coding.wordPairing (l2Generator check)) left right
      _ = 0 := by rw [hleft, hright, add_zero]
  · intro scalar word _hword hword
    calc
      Coding.wordPairing (l2Generator check) (scalar • word) =
          scalar • Coding.wordPairing (l2Generator check) word := by
            exact map_smul (Coding.wordPairing (l2Generator check)) scalar word
      _ = 0 := by rw [hword, smul_zero]
@[simp] theorem phaseState_apply_bit
    (theta : Real) (bit : Fin 2) :
    OneQubitMagic.phaseState theta bit =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude theta ^ bit.val := by
  fin_cases bit <;>
    simp [OneQubitMagic.phaseState_apply_zero,
      OneQubitMagic.phaseState_apply_one]
noncomputable def logicalNegativeAState : LogicalRegister :=
  WithLp.toLp 2 fun bits =>
    (Real.sqrt 2 : Complex)⁻¹ *
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val
@[simp] theorem logicalNegativeAState_apply
    (bits : Bitstring Unit) :
    logicalNegativeAState bits =
      (Real.sqrt 2 : Complex)⁻¹ *
        OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ (bits ()).val :=
  rfl
theorem cssWitness_zCheck_fixed (check : ZCheckIndex) :
    toHermitianQubitOperator (zChecks check) cssWitnessState = cssWitnessState := by
  have hz : l2Generator check ∈ bk15CSSRows.rowCode.dual.carrier :=
    l2Generator_mem_cssRowCodeDual check
  have hP : zChecks check ∈ binaryCSSCheckSet bk15CSSRows.evenCode
      bk15CSSRows.rowCode.dual := by
    exact Or.inr ⟨l2Generator check, hz, rfl⟩
  simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
    binarySupport] using cssWitness_fixed (zChecks check) hP
theorem cssWitness_zProjector_zero :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) cssWitnessState =
      cssWitnessState := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit)) cssWitnessState).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssWitness_zCheck_fixed check
theorem cssWitness_xProjector_zero :
    xProjector (signSyndrome (0 : XCheckIndex → Bit)) cssWitnessState =
      cssWitnessState := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (0 : XCheckIndex → Bit)) cssWitnessState).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssWitness_xCheck_fixed check
theorem aWordCorrectionTransport_zero_symm_apply (psi : BK15Register) :
    (aWordCorrectionTransport (0 : Word)).symm psi = psi := by
  have hfix := aWordCorrectionTransport_zero_apply
    ((aWordCorrectionTransport (0 : Word)).symm psi)
  simpa [UnitaryTransport.symm] using hfix.symm
theorem historyCorrection_zero_symm_apply (psi : BK15Register) :
    (historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm psi = psi := by
  simpa [historyCorrection] using aWordCorrectionTransport_zero_symm_apply psi
noncomputable def acceptedWitnessHistory : History :=
  (signSyndrome (0 : ZCheckIndex → Bit),
    signSyndrome (0 : XCheckIndex → Bit))
theorem acceptedWitnessHistory_outcome :
    historyOutcome acceptedWitnessHistory = .accepted := by
  simp [acceptedWitnessHistory, historyOutcome]
theorem acceptedWitnessHistory_apply :
    historyKraus acceptedWitnessHistory cssWitnessState = cssWitnessState := by
  simp only [acceptedWitnessHistory, historyKraus, Module.End.mul_apply]
  rw [cssWitness_zProjector_zero]
  change xProjector (signSyndrome (0 : XCheckIndex → Bit))
    ((historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm
      cssWitnessState) = cssWitnessState
  rw [historyCorrection_zero_symm_apply, cssWitness_xProjector_zero]
theorem acceptedWitnessHistory_nonzero :
    historyKraus acceptedWitnessHistory ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun hzero cssWitnessState
  rw [acceptedWitnessHistory_apply] at happly
  exact cssWitnessState_ne_zero happly
noncomputable def cssZErrorState (error : Word) : BK15Register :=
  toQubitOperator (cssZCheck error) cssWitnessState
theorem cssZErrorState_ne_zero (error : Word) :
    cssZErrorState error ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun
    (toQubitOperator_adjoint_comp_self (cssZCheck error)) cssWitnessState
  simp only [LinearMap.comp_apply, Module.End.one_apply] at happly
  rw [show toQubitOperator (cssZCheck error) cssWitnessState = 0 by
    simpa [cssZErrorState] using hzero] at happly
  simp at happly
  exact cssWitnessState_ne_zero happly.symm
theorem cssZErrorState_zCheck_fixed (error : Word)
    (check : ZCheckIndex) :
    toHermitianQubitOperator (zChecks check) (cssZErrorState error) =
      cssZErrorState error := by
  have hHermitian :
      toHermitianQubitOperator (zChecks check) =
        toQubitOperator (zChecks check) := by
    simp [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitian]
  have hfixed :
      toQubitOperator (zChecks check) cssWitnessState = cssWitnessState := by
    simpa [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport] using cssWitness_zCheck_fixed check
  have hcomm := toQubitOperator_commute_of_commutes
    (zChecks check) (cssZCheck error)
    (cssZCheck_commutes_cssZCheck _ _)
  have happly := LinearMap.congr_fun hcomm cssWitnessState
  simp only [Module.End.mul_apply] at happly
  rw [hfixed] at happly
  simpa [cssZErrorState] using happly
theorem cssZErrorState_xCheck_eigen (error : Word)
    (check : XCheckIndex) :
    toHermitianQubitOperator (xChecks check) (cssZErrorState error) =
      (signSyndrome (l1Syndrome error) check).sign • cssZErrorState error := by
  have hfixed := cssWitness_xCheck_fixed check
  have hHermitian :
      toHermitianQubitOperator (xChecks check) =
        toQubitOperator (xChecks check) := by
    simp [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport]
  rw [hHermitian]
  have hfixed' :
      toQubitOperator (cssXCheck (linearGenerator check)) cssWitnessState =
        cssWitnessState := by
    simpa [xChecks, toHermitianQubitOperator, hermitianPhaseScalar,
      binaryOverlapCount, binaryOverlapSupport, xSupport, zSupport,
      binarySupport] using hfixed
  by_cases hpair : Coding.wordPairing error (linearGenerator check) = 0
  · have hdot : error ⬝ᵥ linearGenerator check = 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error = 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hcomm :=
      cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero hpair'
    have happly := LinearMap.congr_fun hcomm cssWitnessState
    rw [Module.End.mul_apply, Module.End.mul_apply, hfixed'] at happly
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = 1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [one_smul]
    change toQubitOperator (xChecks check)
        (toQubitOperator (cssZCheck error) cssWitnessState) = _
    simpa [xChecks, cssZErrorState] using happly
  · have hdot : error ⬝ᵥ linearGenerator check ≠ 0 := by
      simpa [Coding.wordPairing_apply] using hpair
    have hpair' : Coding.wordPairing (linearGenerator check) error ≠ 0 := by
      simpa [Coding.wordPairing_apply, dotProduct_comm] using hpair
    have hnotcomm :
        ¬ Commutes (cssXCheck (linearGenerator check)) (cssZCheck error) := by
      simpa [cssXCheck, cssZCheck, Commutes,
        Coding.symplecticForm_x_zero_zero_z_eq_wordPairing] using hpair'
    have hanti := toQubitOperator_anticommute_of_not_commutes
      (cssXCheck (linearGenerator check)) (cssZCheck error) hnotcomm
    have happly := LinearMap.congr_fun hanti cssWitnessState
    simp only [LinearMap.neg_apply, Module.End.mul_apply] at happly
    rw [hfixed'] at happly
    have hsign :
        (signSyndrome (l1Syndrome error) check).sign = -1 := by
      simp [signSyndrome, bitToSign, l1Syndrome, hdot,
        StabilizerOutcome.sign]
    rw [hsign]
    simp only [neg_one_smul]
    change toQubitOperator (xChecks check)
        (toQubitOperator (cssZCheck error) cssWitnessState) = _
    simpa [xChecks, cssZErrorState] using happly
theorem cssZErrorState_zProjector_zero (error : Word) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) (cssZErrorState error) =
      cssZErrorState error := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit)) (cssZErrorState error)).2
  intro check
  simpa [signSyndrome, bitToSign, StabilizerOutcome.sign] using
    cssZErrorState_zCheck_fixed error check
theorem cssZErrorState_xProjector_matching (error : Word) :
    xProjector (signSyndrome (l1Syndrome error)) (cssZErrorState error) =
      cssZErrorState error := by
  apply (jointStabilizerProjector_fixed_iff xChecks xChecks_commute
    (signSyndrome (l1Syndrome error)) (cssZErrorState error)).2
  exact cssZErrorState_xCheck_eigen error
noncomputable def rejectedWitnessHistory (site : Fin 15) : History :=
  (signSyndrome (0 : ZCheckIndex → Bit),
    signSyndrome (l1Syndrome (oneSiteWord site)))
theorem rejectedWitnessHistory_outcome (site : Fin 15) :
    historyOutcome (rejectedWitnessHistory site) = .rejected := by
  simp [rejectedWitnessHistory, historyOutcome,
    oneSiteWord_l1Syndrome_ne_zero site]
theorem rejectedWitnessHistory_apply (site : Fin 15) :
    historyKraus (rejectedWitnessHistory site)
        (cssZErrorState (oneSiteWord site)) =
      cssZErrorState (oneSiteWord site) := by
  simp only [rejectedWitnessHistory, historyKraus, Module.End.mul_apply]
  rw [cssZErrorState_zProjector_zero]
  change xProjector (signSyndrome (l1Syndrome (oneSiteWord site)))
    ((historyCorrection (signSyndrome (0 : ZCheckIndex → Bit))).symm
      (cssZErrorState (oneSiteWord site))) = _
  rw [historyCorrection_zero_symm_apply, cssZErrorState_xProjector_matching]
theorem rejectedWitnessHistory_nonzero (site : Fin 15) :
    historyKraus (rejectedWitnessHistory site) ≠ 0 := by
  intro hzero
  have happly := LinearMap.congr_fun hzero
    (cssZErrorState (oneSiteWord site))
  rw [rejectedWitnessHistory_apply] at happly
  exact cssZErrorState_ne_zero (oneSiteWord site) happly
theorem rawInput_toOperator_sum (epsilon : BK15Epsilon) :
    (rawInput epsilon).toOperator =
      ∑ word : Word, (bk15WordWeight epsilon word : Complex) •
        (InnerProductSpace.rankOne Complex
          (bk15ErrorWordState word) (bk15ErrorWordState word)).toLinearMap := by
  simp [rawInput, bk15ErrorWordMixture, bk15FlatErrorWordMixture,
    DensityOperator.convexCombination_toOperator,
    DensityOperator.convexCombinationOperator,
    bk15ErrorWordDensity_toOperator_rankOne]
theorem comp_sum {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : K →ₗ[Complex] L) (B : index → H →ₗ[Complex] K) :
    A.comp (∑ i, B i) = ∑ i, A.comp (B i) := by
  ext x
  simp
theorem sum_comp {H K L : Type*} {index : Type*}
    [Fintype index]
    [AddCommMonoid H] [AddCommMonoid K] [AddCommMonoid L]
    [Module Complex H] [Module Complex K] [Module Complex L]
    (A : index → K →ₗ[Complex] L) (B : H →ₗ[Complex] K) :
    (∑ i, A i).comp B = ∑ i, (A i).comp B := by
  ext x
  simp
theorem endpointWeight_eq_history_word_sum (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) :
    endpointWeight epsilon outcome =
      ∑ history : History, if historyOutcome history = outcome then
        ∑ word : Word, bk15WordWeight epsilon word *
          ‖historyKraus history (bk15ErrorWordState word)‖ ^ 2
      else 0 := by
  classical
  unfold endpointWeight FiniteInstrument.bornWeight
  rw [FiniteInstrument.branchOperator_apply, rawInput_toOperator_sum]
  simp only [historyInstrument, historyKrausFamily]
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro history _
  by_cases hvisible : historyOutcome history = outcome
  · erw [if_pos hvisible, if_pos hvisible]
    rw [sum_comp, comp_sum, map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [LinearMap.smul_comp, LinearMap.comp_smul,
      sandwich_rankOne, map_smul, InnerProductSpace.trace_rankOne,
      inner_self_eq_norm_sq_to_K]
    simp
    left
    simp [pow_two, Complex.mul_re]
  · erw [if_neg hvisible, if_neg hvisible]
    simp
theorem aInputWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) (bit : Fin 2) :
    0 < aInputWeight epsilon bit := by
  fin_cases bit
  · change 0 < epsilon.cleanWeight
    unfold BK15Epsilon.cleanWeight
    linarith [epsilon.le_half]
  · exact hpositive
theorem bk15WordWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) (word : Word) :
    0 < bk15WordWeight epsilon word := by
  unfold bk15WordWeight
  exact Finset.prod_pos fun site _ =>
    aInputWeight_pos epsilon hpositive (word site)
theorem exists_basis_word_not_annihilated (L : Operator BK15Register)
    (hL : L ≠ 0) :
    ∃ word : Word, L (bk15ErrorWordState word) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hL
  apply Module.Basis.ext bk15AErrorBasis.toBasis
  intro word
  simpa using hall word
set_option maxRecDepth 65536 in
theorem endpointWeight_pos_of_history_nonzero
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon)
    (outcome : DistillationOutcome) (history : History)
    (hvisible : historyOutcome history = outcome)
    (hnonzero : historyKraus history ≠ 0) :
    0 < endpointWeight epsilon outcome := by
  rw [endpointWeight_eq_history_word_sum]
  apply Finset.sum_pos'
  · intro candidate _
    by_cases hcandidate : historyOutcome candidate = outcome
    · rw [if_pos hcandidate]
      exact Finset.sum_nonneg fun word _ =>
        mul_nonneg (bk15WordWeight_nonneg epsilon word) (sq_nonneg _)
    · simp [hcandidate]
  · refine ⟨history, Finset.mem_univ history, ?_⟩
    rw [if_pos hvisible]
    obtain ⟨word, hword⟩ :=
      exists_basis_word_not_annihilated (historyKraus history) hnonzero
    apply Finset.sum_pos'
    · intro candidate _
      exact mul_nonneg (bk15WordWeight_nonneg epsilon candidate) (sq_nonneg _)
    · refine ⟨word, Finset.mem_univ word, ?_⟩
      exact mul_pos (bk15WordWeight_pos epsilon hpositive word)
        (sq_pos_of_pos (norm_pos_iff.mpr hword))
theorem accepted_endpointWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < endpointWeight epsilon .accepted :=
  endpointWeight_pos_of_history_nonzero epsilon hpositive .accepted
    acceptedWitnessHistory acceptedWitnessHistory_outcome
    acceptedWitnessHistory_nonzero
theorem rejected_endpointWeight_pos (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    0 < endpointWeight epsilon .rejected :=
  endpointWeight_pos_of_history_nonzero epsilon hpositive .rejected
    (rejectedWitnessHistory 0) (rejectedWitnessHistory_outcome 0)
    (rejectedWitnessHistory_nonzero 0)
def logicalBitEquiv : Bitstring Unit ≃ Fin 2 where
  toFun bits := flipBit (bits ())
  invFun bit := fun _ => flipBit bit
  left_inv := by
    intro bits
    funext site
    cases site
    simp
  right_inv := by
    intro bit
    simp
noncomputable def logicalRegisterToQubit :
    UnitaryTransport LogicalRegister QubitSpace := by
  let sourceBasis := EuclideanSpace.basisFun (Bitstring Unit) Complex
  let targetBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let U := sourceBasis.equiv targetBasis logicalBitEquiv
  exact { toLinearEquiv := U.toLinearEquiv, map_inner := U.inner_map_map }
@[simp] theorem logicalRegisterToQubit_basis (bit : Fin 2) :
    logicalRegisterToQubit
        (EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => bit)) =
      EuclideanSpace.basisFun (Fin 2) Complex (flipBit bit) := by
  change ((EuclideanSpace.basisFun (Bitstring Unit) Complex).equiv
    (EuclideanSpace.basisFun (Fin 2) Complex) logicalBitEquiv)
      (EuclideanSpace.basisFun (Bitstring Unit) Complex (fun _ => bit)) = _
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
noncomputable def decoderToQubitChannel : QuantumChannel BK15Register QubitSpace :=
  QuantumChannel.comp (QuantumChannel.unitaryConj logicalRegisterToQubit)
    decoderChannel
noncomputable def decodedOperation : QuantumChannel BK15Register QubitSpace :=
  QuantumChannel.comp decoderToQubitChannel historyChannel
noncomputable def endpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator BK15Register :=
  historyInstrument.conditionalDensity outcome (rawInput epsilon) hpositive
set_option maxRecDepth 262144 in
set_option maxHeartbeats 800000 in
@[simp] theorem endpointConditional_toOperator (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    (endpointConditional epsilon outcome hpositive).toOperator =
      ((endpointWeight epsilon outcome : Complex)⁻¹) • rawEndpoint epsilon outcome := by
  rfl
set_option maxRecDepth 262144 in
set_option maxHeartbeats 800000 in
/-- Weighting a positive conditional endpoint reconstructs its literal raw
branch. -/
theorem endpointWeight_smul_endpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    (endpointWeight epsilon outcome : Complex) •
      (endpointConditional epsilon outcome hpositive).toOperator =
        rawEndpoint epsilon outcome := by
  rw [endpointConditional_toOperator]
  simp [smul_smul, hpositive.ne']
theorem weighted_endpointConditionals_reconstruct
    (epsilon : BK15Epsilon)
    (haccepted : 0 < endpointWeight epsilon .accepted)
    (hrejected : 0 < endpointWeight epsilon .rejected) :
    (endpointWeight epsilon .accepted : Complex) •
        (endpointConditional epsilon .accepted haccepted).toOperator +
      (endpointWeight epsilon .rejected : Complex) •
        (endpointConditional epsilon .rejected hrejected).toOperator =
      (historyChannel.mapDensity (rawInput epsilon)).toOperator := by
  rw [endpointWeight_smul_endpointConditional,
    endpointWeight_smul_endpointConditional]
  exact rawEndpoints_reconstruct epsilon
noncomputable def decodedEndpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator LogicalRegister :=
  decoderChannel.mapDensity (endpointConditional epsilon outcome hpositive)
noncomputable def qubitEndpointConditional (epsilon : BK15Epsilon)
    (outcome : DistillationOutcome) (hpositive : 0 < endpointWeight epsilon outcome) :
    DensityOperator QubitSpace :=
  logicalRegisterToQubit.conjDensity
    (decodedEndpointConditional epsilon outcome hpositive)
theorem physicalRun_output_decomposition
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    historyChannel.mapDensity
        (bk15PrepareInput (bk15NoisyResources epsilon)) =
      outcomeMixture (endpointWeight epsilon .accepted)
        (endpointWeight_nonneg epsilon .accepted)
        (by
          linarith [endpointWeight_nonneg epsilon .rejected,
            endpointWeights_sum epsilon])
        (endpointConditional epsilon .accepted
          (accepted_endpointWeight_pos epsilon hpositive))
        (endpointConditional epsilon .rejected
          (rejected_endpointWeight_pos epsilon hpositive)) := by
  have hmixture (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1)
      (rho sigma : DensityOperator BK15Register) :
      (outcomeMixture p h0 h1 rho sigma).toOperator =
        (p : Complex) • rho.toOperator + ((1 - p : ℝ) : Complex) • sigma.toOperator := by
    simp [outcomeMixture, DensityOperator.convexCombinationOperator,
      branchState, outcomeWeight,
      show (Finset.univ : Finset DistillationOutcome) =
        {.accepted, .rejected} by decide]
    rw [RCLike.real_smul_eq_coe_smul (K := Complex)]
    change ((1 - p : ℝ) : Complex) • sigma.toOperator =
      (1 - (p : Complex)) • sigma.toOperator
    exact congrArg (fun c : Complex => c • sigma.toOperator)
      (by simp only [Complex.ofReal_sub, Complex.ofReal_one])
  apply DensityOperator.ext_toOperator
  rw [bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture]
  change (historyChannel.mapDensity (rawInput epsilon)).toOperator = _
  rw [← weighted_endpointConditionals_reconstruct epsilon
    (accepted_endpointWeight_pos epsilon hpositive)
    (rejected_endpointWeight_pos epsilon hpositive)]
  have hreject :
      1 - endpointWeight epsilon .accepted =
        endpointWeight epsilon .rejected := by
    linarith [endpointWeights_sum epsilon]
  rw [hmixture, hreject]
noncomputable def physicalRun (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    DistillationRun QubitSpace BK15Register BK15Register where
  resourceCount := 15
  noisyInput := bk15NoisyResources epsilon
  prepareInput := bk15PrepareInput
  operation := historyChannel
  successProbability := endpointWeight epsilon .accepted
  success_nonneg := endpointWeight_nonneg epsilon .accepted
  success_le_one := by
    linarith [endpointWeight_nonneg epsilon .rejected,
      endpointWeights_sum epsilon]
  acceptedOutput := endpointConditional epsilon .accepted
    (accepted_endpointWeight_pos epsilon hpositive)
  rejectedOutput := endpointConditional epsilon .rejected
    (rejected_endpointWeight_pos epsilon hpositive)
  output_decomposition := physicalRun_output_decomposition epsilon hpositive
noncomputable def bk15Run (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    DistillationRun QubitSpace BK15Register QubitSpace :=
  (physicalRun epsilon hpositive).postprocess decoderToQubitChannel
def bk15InputErrorModel (epsilon : BK15Epsilon) :
    InputErrorModel 15 QubitSpace :=
  .independent
    { rate := fun _ => epsilon.epsilon
      rate_nonneg := fun _ => epsilon.nonneg
      rate_le_one := fun _ => epsilon.le_one
      admissible := fun rates inputs =>
        ∀ site, rates site = epsilon.epsilon ∧
          inputs site = bk15NoisyResources epsilon site }
theorem bk15InputErrorModel_permits (epsilon : BK15Epsilon) :
    (bk15InputErrorModel epsilon).Permits
      (bk15NoisyResources epsilon) := by
  change ∀ site, (fun _ => epsilon.epsilon) site = epsilon.epsilon ∧
    bk15NoisyResources epsilon site = bk15NoisyResources epsilon site
  intro site
  exact ⟨rfl, rfl⟩
def bk15OutputError
    (rho _ideal : DensityOperator QubitSpace) : Real :=
  aInputError rho
theorem aInputError_nonneg (rho : DensityOperator QubitSpace) :
    0 ≤ aInputError rho := by
  unfold aInputError
  exact sub_nonneg.mpr
    (OneQubitMagic.projectionSquaredOverlap_le_one
      (aBasisProjector .positive) rho
      (aBasisProjector_isSymmetricProjection .positive))
theorem bk15OutputError_nonneg
    (rho ideal : DensityOperator QubitSpace) :
    0 ≤ bk15OutputError rho ideal :=
  aInputError_nonneg rho
noncomputable def bk15MagicStateProtocol (epsilon : BK15Epsilon)
    (hpositive : 0 < epsilon.epsilon) :
    MagicStateDistillationProtocol QubitSpace BK15Register QubitSpace where
  run := bk15Run epsilon hpositive
  inputErrorModel := bk15InputErrorModel epsilon
  inputPermitted := bk15InputErrorModel_permits epsilon
  behavior := .postselected
  idealOutput := aZeroDensity
  outputError := bk15OutputError
  outputError_nonneg := bk15OutputError_nonneg
def zeroEpsilon : BK15Epsilon where
  epsilon := 0
  nonneg := le_rfl
  le_half := by norm_num
def zeroErrorWord : Word := 0
end Protocol
end BK15
end Distillation
end QEC


