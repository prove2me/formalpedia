-- Prove2me | Definitions.Def_QEC_Distillation_BK15_EndpointPart1_QECert
-- name    : QEC_Distillation_BK15_EndpointPart1_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:21:40.486267+00:00
-- url     : https://prove2.me/theorems/eac26b52-2282-47ee-a279-94276e3e40f5
-- title:
--   BK15 accepted endpoint exact helper part 1
-- statement:
--   Source-exact checked intermediate declarations for the BK15 accepted endpoint formula.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean#L1630-L1656

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_BK15_Protocol_aWordCorrectionTransport_eigen
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
import Theorems.Thm_QEC_Distillation_BK15_l1_dimension
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_l1Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_l2Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_mem_l1DualWords_iff
import Theorems.Thm_QEC_Distillation_BK15_mem_l2_dual_iff_exists_l1_plus_allOnes
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
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
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
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
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


section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
private theorem bk15TensorErrorState_eq_errorVector (error : Word) :
    bk15TensorErrorState error = bk15TensorErrorVector error := by
  rfl
private theorem fin15Nested_eq_prod (f : Fin 15 → Complex) :
    fin15Nested f = ∏ site, f site := by
  simp [fin15Nested, Fin.prod_univ_succ]
private theorem inner_tmul_complex
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Complex E]
    [NormedAddCommGroup F] [InnerProductSpace Complex F]
    (x x' : E) (y y' : F) :
    inner Complex (x ⊗ₜ[Complex] y) (x' ⊗ₜ[Complex] y') =
      inner Complex x x' * inner Complex y y' := by
  exact TensorProduct.inner_tmul Complex x x' y y'
set_option maxRecDepth 65536 in
private theorem bk15Tensor_inner_nested
    (error : Word) (bits : Bitstring (Fin 15)) :
    inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorState error) =
      fin15Nested
        (fun site => aInputState (error site) (bits site)) := by
  calc
    inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorState error) =
      inner Complex
        (bk15TensorComputationalBasis (splitBK15Bitstring bits))
        (bk15TensorErrorVector error) := by
          exact congrArg
            (fun psi : BK15Tensor => inner Complex
              (bk15TensorComputationalBasis
                (splitBK15Bitstring bits)) psi)
            (bk15TensorErrorState_eq_errorVector error)
    _ = fin15Nested
        (fun site => aInputState (error site) (bits site)) := by
      unfold fin15Nested bk15TensorErrorVector
      rw [bk15TensorComputationalBasis_apply]
      unfold tensor15Vector
      simp only [splitBK15Bitstring]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      rw [inner_tmul_complex]
      simp only [EuclideanSpace.basisFun_inner, wordBits_apply]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem bk15ErrorWordState_apply_product
    (error : Word) (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState error bits =
      ∏ site : Fin 15, aInputState (error site) (bits site) := by
  have hinner := bk15TensorRegisterTransport.map_inner
    (bk15TensorComputationalBasis (splitBK15Bitstring bits))
    (bk15TensorErrorState error)
  rw [bk15TensorRegisterTransport_apply_computationalBasis,
    bk15TupleBitstring_splitBK15Bitstring,
    EuclideanSpace.basisFun_inner] at hinner
  change bk15ErrorWordState error bits =
    inner Complex
      (bk15TensorComputationalBasis (splitBK15Bitstring bits))
      (bk15TensorErrorState error) at hinner
  rw [bk15Tensor_inner_nested] at hinner
  exact hinner.trans (fin15Nested_eq_prod _)
private theorem bitstringWordEquiv_apply_eq_finBitToBit
    (bits : Bitstring (Fin 15)) (site : Fin 15) :
    bitstringWordEquiv (Fin 15) bits site = finBitToBit (bits site) := by
  rw [bitstringWordEquiv_apply]
  generalize hbit : bits site = bit
  fin_cases bit <;> rfl
private theorem binaryPhaseScalar_finBitToBit (bit : Fin 2) :
    binaryPhaseScalar (finBitToBit bit) = zPhase bit := by
  fin_cases bit <;> rfl
private theorem binaryPhaseScalar_mul_aInputState_apply
    (check error : Bit) (bit : Fin 2) :
    binaryPhaseScalar (check * finBitToBit bit) * aInputState error bit =
      aInputState (error + check) bit := by
  by_cases hcheck : check = 0
  · subst check
    simp
  · have hcheck_one : check = 1 := zmod_two_eq_one_of_ne_zero hcheck
    subst check
    by_cases herror : error = 0
    · subst error
      simpa [aInputState, aOneState_eq_pauliZ,
        binaryPhaseScalar_finBitToBit] using
          (pauliZ_apply aZeroState bit).symm
    · have herror_one : error = 1 := zmod_two_eq_one_of_ne_zero herror
      subst error
      have hone : (1 : Bit) + 1 = 0 := by decide
      rw [hone]
      simp [aInputState, aOneState_eq_pauliZ,
        binaryPhaseScalar_finBitToBit, pauliZ_apply, ← mul_assoc]
set_option maxRecDepth 65536 in
theorem cssZCheck_errorWord_QECertEndpoint (check error : Word) :
    toHermitianQubitOperator (cssZCheck check) (bk15ErrorWordState error) =
      bk15ErrorWordState (error + check) := by
  ext bits
  simp [toHermitianQubitOperator, hermitianPhaseScalar,
    toQubitOperator, xSupport, zSupport, binaryOverlapCount,
    binaryOverlapSupport, bk15ErrorWordState_apply_product]
  rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing,
    Coding.wordPairing_apply, dotProduct, binaryPhaseScalar_sum,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro site _
  rw [bitstringWordEquiv_apply_eq_finBitToBit]
  exact binaryPhaseScalar_mul_aInputState_apply
    (check site) (error site) (bits site)
theorem aWordCorrectionTransport_symm_eigen_QECertEndpoint (word error : Word) :
    (aWordCorrectionTransport word).symm (bk15ErrorWordState error) =
      binaryPhaseScalar (word ⬝ᵥ error) • bk15ErrorWordState error := by
  let U := aWordCorrectionTransport word
  let scalar := binaryPhaseScalar (word ⬝ᵥ error)
  have hforward : U (bk15ErrorWordState error) =
      scalar • bk15ErrorWordState error := by
    exact aWordCorrectionTransport_eigen word error
  have hback := congrArg (fun psi : BK15Register => U.symm psi) hforward
  simp only [map_smul] at hback
  have hstate : bk15ErrorWordState error =
      scalar • U.symm (bk15ErrorWordState error) := by
    simpa [U, UnitaryTransport.symm] using hback
  calc
    U.symm (bk15ErrorWordState error) =
        1 • U.symm (bk15ErrorWordState error) := by simp
    _ = (scalar * scalar) • U.symm (bk15ErrorWordState error) := by
      simp [scalar, binaryPhaseScalar_mul_self]
    _ = scalar • (scalar • U.symm (bk15ErrorWordState error)) := by
      rw [smul_smul]
    _ = scalar • bk15ErrorWordState error := by rw [← hstate]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem aWordCorrectionTransport_symm_cssZCheck_QECertEndpoint
    (word check : Word) :
    (aWordCorrectionTransport word).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck check) =
      binaryPhaseScalar (word ⬝ᵥ check) •
        (toHermitianQubitOperator (cssZCheck check) *
          (aWordCorrectionTransport word).symm.toLinearEquiv.toLinearMap) := by
  apply Module.Basis.ext bk15AErrorBasis.toBasis
  intro error
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  change (aWordCorrectionTransport word).symm
      (toHermitianQubitOperator (cssZCheck check)
        (bk15AErrorBasis error)) =
    binaryPhaseScalar (word ⬝ᵥ check) •
      toHermitianQubitOperator (cssZCheck check)
        ((aWordCorrectionTransport word).symm
          (bk15AErrorBasis error))
  rw [bk15AErrorBasis_apply, cssZCheck_errorWord_QECertEndpoint,
    aWordCorrectionTransport_symm_eigen_QECertEndpoint,
    aWordCorrectionTransport_symm_eigen_QECertEndpoint, map_smul,
    cssZCheck_errorWord_QECertEndpoint]
  rw [dotProduct_add, binaryPhaseScalar_add]
  module
theorem jointStabilizerProjector_intertwines_operator_QECertEndpoint
    {index checkIndex : Type} [Fintype index] [DecidableEq index]
    [Fintype checkIndex] [DecidableEq checkIndex]
    (checks : checkIndex → Binary index)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (T : Operator (QubitRegister index))
    (source target : JointSyndrome checkIndex)
    (hfactor : ∀ check,
      T * jointStabilizerFactor checks source check =
        jointStabilizerFactor checks target check * T) :
    T * jointStabilizerProjector checks hcomm source =
      jointStabilizerProjector checks hcomm target * T := by
  classical
  let pairFactor : checkIndex →
      Operator (QubitRegister index) × Operator (QubitRegister index) :=
    fun check =>
      (jointStabilizerFactor checks source check,
        jointStabilizerFactor checks target check)
  have hpairwise :
      (↑(Finset.univ : Finset checkIndex) : Set checkIndex).Pairwise
      (Function.onFun Commute pairFactor) := by
    intro left _ right _ hne
    change pairFactor left * pairFactor right =
      pairFactor right * pairFactor left
    apply Prod.ext
    · exact
        (jointStabilizerFactor_commute checks hcomm left right source source).eq
    · exact
        (jointStabilizerFactor_commute checks hcomm left right target target).eq
  let productPair := Finset.univ.noncommProd pairFactor hpairwise
  have hintertwines : T * productPair.1 = productPair.2 * T := by
    dsimp only [productPair]
    refine Finset.noncommProd_induction Finset.univ pairFactor hpairwise
      (fun pair => T * pair.1 = pair.2 * T) ?_ ?_ ?_
    · intro left right hleft hright
      change T * (left.1 * right.1) = (left.2 * right.2) * T
      calc
        T * (left.1 * right.1) = (T * left.1) * right.1 := by
          rw [mul_assoc]
        _ = (left.2 * T) * right.1 := by rw [hleft]
        _ = left.2 * (T * right.1) := by rw [mul_assoc]
        _ = left.2 * (right.2 * T) := by rw [hright]
        _ = (left.2 * right.2) * T := by rw [mul_assoc]
    · simp
    · intro check _
      exact hfactor check
  have hfst : productPair.1 =
      jointStabilizerProjector checks hcomm source := by
    dsimp only [productPair]
    unfold jointStabilizerProjector
    simpa [pairFactor] using
      (Finset.map_noncommProd Finset.univ pairFactor hpairwise
        (MonoidHom.fst _ _))
  have hsnd : productPair.2 =
      jointStabilizerProjector checks hcomm target := by
    dsimp only [productPair]
    unfold jointStabilizerProjector
    simpa [pairFactor] using
      (Finset.map_noncommProd Finset.univ pairFactor hpairwise
        (MonoidHom.snd _ _))
  simpa [hfst, hsnd] using hintertwines
private theorem historyCorrection_phase
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    binaryPhaseScalar
        (l2SyndromeSection (zBinarySyndrome outcome) ⬝ᵥ l2Generator check) =
      (outcome check).sign := by
  have hsection := congrFun
    (l2SyndromeSection_apply (zBinarySyndrome outcome)) check
  change Coding.wordPairing (l2SyndromeSection (zBinarySyndrome outcome))
      (l2Generator check) = zBinarySyndrome outcome check at hsection
  rw [Coding.wordPairing_apply] at hsection
  rw [hsection]
  exact binaryPhaseScalar_signToBit (outcome check)
private theorem historyCorrection_symm_zCheck
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (zChecks check) =
      (outcome check).sign •
        (toHermitianQubitOperator (zChecks check) *
          (historyCorrection outcome).symm.toLinearEquiv.toLinearMap) := by
  change
    (aWordCorrectionTransport
        (l2SyndromeSection
          (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap *
        toHermitianQubitOperator (cssZCheck (l2Generator check)) =
      (outcome check).sign •
        (toHermitianQubitOperator (cssZCheck (l2Generator check)) *
          (aWordCorrectionTransport
            (l2SyndromeSection
              (zBinarySyndrome outcome))).symm.toLinearEquiv.toLinearMap)
  rw [aWordCorrectionTransport_symm_cssZCheck_QECertEndpoint,
    historyCorrection_phase]
private theorem historyCorrection_symm_zFactor
    (outcome : ZJointSyndrome) (check : ZCheckIndex) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        jointStabilizerFactor zChecks outcome check =
      jointStabilizerFactor zChecks
          (signSyndrome (0 : ZCheckIndex → Bit)) check *
        (historyCorrection outcome).symm.toLinearEquiv.toLinearMap := by
  let T := (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
  let S := toHermitianQubitOperator (zChecks check)
  let scalar := (outcome check).sign
  have hcheck : T * S = scalar • (S * T) := by
    exact historyCorrection_symm_zCheck outcome check
  have hscalar : scalar * scalar = 1 := by
    exact StabilizerOutcome.sign_mul_self (outcome check)
  simp only [jointStabilizerFactor, stabilizerProjector, signSyndrome,
    bitToSign, StabilizerOutcome.sign, Pi.zero_apply, if_pos, one_smul]
  change T * ((1 / 2 : Complex) • (1 + scalar • S)) =
    ((1 / 2 : Complex) • (1 + S)) * T
  calc
    T * ((1 / 2 : Complex) • (1 + scalar • S)) =
        (1 / 2 : Complex) • (T + scalar • (T * S)) := by
      simp only [mul_smul_comm, mul_add, mul_one]
    _ = (1 / 2 : Complex) •
        (T + scalar • (scalar • (S * T))) := by rw [hcheck]
    _ = (1 / 2 : Complex) • (T + S * T) := by
      rw [smul_smul, hscalar, one_smul]
    _ = ((1 / 2 : Complex) • (1 + S)) * T := by
      simp only [smul_mul_assoc, add_mul, one_mul]
theorem historyCorrection_symm_zProjector_QECertEndpoint
    (outcome : ZJointSyndrome) :
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap *
        zProjector outcome =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit)) *
        (historyCorrection outcome).symm.toLinearEquiv.toLinearMap := by
  exact jointStabilizerProjector_intertwines_operator_QECertEndpoint
    zChecks zChecks_commute
    (historyCorrection outcome).symm.toLinearEquiv.toLinearMap
    outcome (signSyndrome (0 : ZCheckIndex → Bit))
    (historyCorrection_symm_zFactor outcome)
private theorem zCheck_computationalBasis_eigen
    (check : ZCheckIndex) (bits : Bitstring (Fin 15)) :
    toHermitianQubitOperator (zChecks check)
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      (signSyndrome
          (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign •
        EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  ext candidate
  simp [zChecks, toHermitianQubitOperator, hermitianPhaseScalar,
    cssZCheck, toQubitOperator, xSupport, zSupport, binaryOverlapCount,
    binaryOverlapSupport, binarySupport, signSyndrome, bitToSign,
    StabilizerOutcome.sign, l2Syndrome, Coding.wordPairing_apply,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hcandidate : candidate = bits
  · subst candidate
    simp only [if_pos]
    have hsupport : ({x | ¬l2Generator check x = 0} : Finset (Fin 15)) =
        binarySupport (l2Generator check) := by
      ext site
      simp [binarySupport]
    erw [hsupport]
    rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing,
      Coding.wordPairing_apply, dotProduct_comm]
    by_cases hzero :
        (bitstringWordEquiv (Fin 15)) bits ⬝ᵥ l2Generator check = 0 <;>
      simp [hzero, binaryPhaseScalar]
  · simp [hcandidate]
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_computationalBasis_of_zero
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  apply (jointStabilizerProjector_fixed_iff zChecks zChecks_commute
    (signSyndrome (0 : ZCheckIndex → Bit))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)).2
  intro check
  have hcheck := congrFun hzero check
  have hsign : (signSyndrome
      (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign = 1 := by
    simp [signSyndrome, bitToSign, hcheck, StabilizerOutcome.sign]
  have heigen := zCheck_computationalBasis_eigen check bits
  rw [hsign, one_smul] at heigen
  have hzeroSign :
      (signSyndrome (0 : ZCheckIndex → Bit) check).sign = 1 := by
    simp [signSyndrome, bitToSign, StabilizerOutcome.sign]
  rw [hzeroSign, one_smul]
  exact heigen
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_mul_zCheck (check : ZCheckIndex) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) *
        toHermitianQubitOperator (zChecks check) =
      zProjector (signSyndrome (0 : ZCheckIndex → Bit)) := by
  have hleft :
      toHermitianQubitOperator (zChecks check) *
          zProjector (signSyndrome (0 : ZCheckIndex → Bit)) =
        zProjector (signSyndrome (0 : ZCheckIndex → Bit)) := by
    have hsign :
        (signSyndrome (0 : ZCheckIndex → Bit) check).sign = 1 := by
      simp [signSyndrome, bitToSign, StabilizerOutcome.sign]
    have heigen := jointStabilizerProjector_eigen zChecks zChecks_commute
      (signSyndrome (0 : ZCheckIndex → Bit)) check
    rw [hsign, one_smul] at heigen
    exact heigen
  have hadjoint := congrArg LinearMap.adjoint hleft
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    adjoint_toHermitianQubitOperator_eq_self, zProjector_adjoint] using hadjoint
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zCheck_computationalBasis_negative
    (check : ZCheckIndex) (bits : Bitstring (Fin 15))
    (hcheck : l2Syndrome (bitstringWordEquiv (Fin 15) bits) check ≠ 0) :
    toHermitianQubitOperator (zChecks check)
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      -EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits := by
  have hsign :
      (signSyndrome
        (l2Syndrome (bitstringWordEquiv (Fin 15) bits)) check).sign = -1 := by
    simp [signSyndrome, bitToSign, hcheck, StabilizerOutcome.sign]
  have heigen := zCheck_computationalBasis_eigen check bits
  rw [hsign, neg_one_smul] at heigen
  exact heigen
private theorem eq_zero_of_neg_eq_self_complex
    {V : Type} [AddCommGroup V] [Module Complex V]
    (value : V) (hneg : -value = value) : value = 0 := by
  have hsum : value + value = 0 := neg_eq_iff_add_eq_zero.mp hneg
  have htwo : (2 : Complex) • value = 0 := by
    simpa [two_smul] using hsum
  rcases smul_eq_zero.mp htwo with hscalar | hvalue
  · norm_num at hscalar
  · exact hvalue
private theorem projector_apply_eq_zero_of_neg_eigen
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace Complex V]
    (projector observable : Module.End Complex V) (value : V)
    (hmul : projector * observable = projector)
    (heigen : observable value = -value) : projector value = 0 := by
  have happly := LinearMap.congr_fun hmul value
  simp only [Module.End.mul_apply] at happly
  rw [heigen] at happly
  simp only [map_neg] at happly
  exact eq_zero_of_neg_eq_self_complex _ happly
private theorem exists_l2Syndrome_check_ne_zero
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) ≠ 0) :
    ∃ check, l2Syndrome (bitstringWordEquiv (Fin 15) bits) check ≠ 0 := by
  classical
  by_contra hall
  apply hzero
  funext check
  by_contra hcheck
  exact hall ⟨check, hcheck⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private theorem zProjector_zero_computationalBasis_of_ne
    (bits : Bitstring (Fin 15))
    (hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) ≠ 0) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) = 0 := by
  obtain ⟨check, hcheck⟩ := exists_l2Syndrome_check_ne_zero bits hzero
  exact projector_apply_eq_zero_of_neg_eigen
    (zProjector (signSyndrome (0 : ZCheckIndex → Bit)))
    (toHermitianQubitOperator (zChecks check))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits)
    (zProjector_zero_mul_zCheck check)
    (zCheck_computationalBasis_negative check bits hcheck)
private theorem zProjector_zero_computationalBasis
    (bits : Bitstring (Fin 15)) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit))
        (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) =
      if l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 then
        EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits
      else 0 := by
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    exact zProjector_zero_computationalBasis_of_zero bits hzero
  · rw [if_neg hzero]
    exact zProjector_zero_computationalBasis_of_ne bits hzero
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem zProjector_zero_apply_QECertEndpoint
    (psi : BK15Register) (bits : Bitstring (Fin 15)) :
    zProjector (signSyndrome (0 : ZCheckIndex → Bit)) psi bits =
      if l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0 then
        psi bits
      else 0 := by
  have hinner := LinearMap.adjoint_inner_right
    (zProjector (signSyndrome (0 : ZCheckIndex → Bit)))
    (EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex bits) psi
  rw [zProjector_adjoint] at hinner
  rw [zProjector_zero_computationalBasis] at hinner
  by_cases hzero : l2Syndrome (bitstringWordEquiv (Fin 15) bits) = 0
  · rw [if_pos hzero]
    rw [if_pos hzero] at hinner
    rw [EuclideanSpace.basisFun_inner,
      EuclideanSpace.basisFun_inner] at hinner
    exact hinner
  · rw [if_neg hzero]
    rw [if_neg hzero] at hinner
    rw [EuclideanSpace.basisFun_inner] at hinner
    simpa using hinner
private theorem l2Generator_mem_cssRowCodeDual (check : ZCheckIndex) :
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
set_option maxRecDepth 65536 in
private theorem bk15IdealState_apply_product
    (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState (0 : Word) bits =
      ∏ site : Fin 15, aZeroState (bits site) := by
  simpa [aInputState] using
    bk15ErrorWordState_apply_product (0 : Word) bits
private theorem bit_sum_eq_hammingWeight
    (bits : Bitstring (Fin 15)) :
    (∑ site : Fin 15, (bits site).val) =
      Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) := by
  classical
  rw [Coding.HammingWeight, Coding.hammingSupport,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro site _
  generalize hbit : bits site = bit
  fin_cases bit
  · simp [hbit]
    rfl
  · simp [hbit]
    exact one_ne_zero
set_option maxRecDepth 65536 in
theorem bk15IdealState_apply_QECertEndpoint
    (bits : Bitstring (Fin 15)) :
    bk15ErrorWordState (0 : Word) bits =
      (Real.sqrt 2 : Complex)⁻¹ ^ 15 *
        OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
          Coding.HammingWeight (bitstringWordEquiv (Fin 15) bits) := by
  rw [bk15IdealState_apply_product]
  simp_rw [aZeroState, phaseState_apply_bit]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, Finset.card_univ, Fintype.card_fin,
    bit_sum_eq_hammingWeight]
private theorem bk15_evenCode_eq_L1 :
    bk15CSSRows.evenCode.carrier = L1.carrier := by
  change Submodule.span Bit (Set.range linearGenerator) =
    LinearMap.range l1CoefficientMap
  ext word
  constructor
  · intro hword
    obtain ⟨a, ha⟩ :=
      (Submodule.mem_span_range_iff_exists_fun Bit).1 hword
    refine ⟨a, ?_⟩
    rw [l1CoefficientMap_eq_sum]
    exact ha
  · rintro ⟨a, rfl⟩
    apply (Submodule.mem_span_range_iff_exists_fun Bit).2
    exact ⟨a, (l1CoefficientMap_eq_sum a).symm⟩
private theorem bk15_evenCode_card :
    Nat.card bk15CSSRows.evenCode.carrier = 16 := by
  rw [bk15_evenCode_eq_L1,
    Module.natCard_eq_pow_finrank (K := Bit) (V := L1.carrier)]
  change Nat.card Bit ^ Coding.Dimension L1 = 16
  rw [l1_dimension]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]
theorem bk15_cssNormalizationScalar_QECertEndpoint :
    bk15CSSRows.cssNormalizationScalar = (4 : Complex)⁻¹ := by
  rw [Triorthogonal.BinaryRowFamily.cssNormalizationScalar,
    bk15_evenCode_card]
  norm_num
theorem logical_const_bit_val_QECertEndpoint (c : Bit) :
    (((bitstringWordEquiv Unit).symm (fun _ => c)) ()).val = c.val := by
  fin_cases c <;> rfl
theorem logicalLabel_l1_plus_allOnes_QECertEndpoint
    (a : Fin 4 → Bit) (c : Bit)
    (hmem : l1CoefficientMap a + c • allOnes ∈
      bk15CSSRows.rowCode.dual.dual.carrier) :
    (bk15CSSRows.logicalBasisEquivLogicalQuotient
        bk15CSSRows_triorthogonal).symm
        (Submodule.Quotient.mk
          (⟨l1CoefficientMap a + c • allOnes, hmem⟩ :
            bk15CSSRows.rowCode.dual.dual.carrier)) =
      (bitstringWordEquiv Unit).symm (fun _ => c) := by
  apply (bk15CSSRows.logicalBasisEquivLogicalQuotient
    bk15CSSRows_triorthogonal).injective
  rw [Equiv.apply_symm_apply]
  simp only [Triorthogonal.BinaryRowFamily.logicalBasisEquivLogicalQuotient,
    LinearEquiv.coe_toEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply]
  rw [Triorthogonal.BinaryRowFamily.oddWordToLogicalQuotient]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  have hl1 : l1CoefficientMap a ∈ bk15CSSRows.evenCode.carrier := by
    rw [bk15_evenCode_eq_L1]
    exact ⟨a, rfl⟩
  change l1CoefficientMap a + c • allOnes -
      bk15CSSRows.oddCombination (fun _ => c) ∈
    bk15CSSRows.evenCode.carrier
  have hodd : bk15CSSRows.oddCombination (fun _ => c) =
      c • allOnes := by
    rw [Triorthogonal.BinaryRowFamily.oddCombination_apply]
    simp [bk15CSSRows]
  rw [hodd, add_sub_cancel_right]
  exact hl1
private theorem phaseAmplitude_two_pi_mul_int_bk15 (k : Int) :
    OneQubitMagic.phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
  unfold OneQubitMagic.phaseAmplitude
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  all_goals push_cast
  all_goals ring_nf
private theorem phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
    (m n : Int) (h : (m : ZMod 8) = (n : ZMod 8)) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4 * (m : Real)) =
      OneQubitMagic.phaseAmplitude (Real.pi / 4 * (n : Real)) := by
  have hmod : m ≡ n [ZMOD (8 : Int)] :=
    (ZMod.intCast_eq_intCast_iff m n 8).mp h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  have hnm : n = m + 8 * k := by omega
  have hangle :
      Real.pi / 4 * (n : Real) =
        Real.pi / 4 * (m : Real) + (2 * Real.pi) * (k : Real) := by
    rw [hnm]
    push_cast
    ring
  rw [hangle, OneQubitMagic.phaseAmplitude_add,
    phaseAmplitude_two_pi_mul_int_bk15, mul_one]
private theorem phaseAmplitude_pow_bk15 (theta : Real) (n : Nat) :
    OneQubitMagic.phaseAmplitude theta ^ n =
      OneQubitMagic.phaseAmplitude ((n : Real) * theta) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← OneQubitMagic.phaseAmplitude_add]
      congr 2
      push_cast
      ring
private theorem l1_weight_cast8 (a : Fin 4 → Bit) :
    (Coding.HammingWeight (l1CoefficientMap a) : ZMod 8) = 0 := by
  decide +kernel +revert
private theorem l1_plus_allOnes_weight_cast8 (a : Fin 4 → Bit) :
    (Coding.HammingWeight (l1CoefficientMap a + allOnes) : ZMod 8) = -1 := by
  decide +kernel +revert
theorem l1_plus_allOnes_phase_QECertEndpoint (a : Fin 4 → Bit) (c : Bit) :
    OneQubitMagic.phaseAmplitude (Real.pi / 4) ^
        Coding.HammingWeight (l1CoefficientMap a + c • allOnes) =
      OneQubitMagic.phaseAmplitude (-Real.pi / 4) ^ c.val := by
  by_cases hc : c = 0
  · rw [hc]
    simp only [zero_smul, add_zero, ZMod.val_zero, pow_zero]
    rw [phaseAmplitude_pow_bk15]
    have hphase := phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
      (Coding.HammingWeight (l1CoefficientMap a) : Int) 0 (by
        simpa using l1_weight_cast8 a)
    simpa [mul_comm] using hphase
  · have hc1 : c = 1 := by
      fin_cases c
      · exact (hc rfl).elim
      · rfl
    rw [hc1]
    simp only [one_smul, ZMod.val_one, pow_one]
    rw [phaseAmplitude_pow_bk15]
    have hphase := phaseAmplitude_pi_div_four_int_eq_of_cast_eq_bk15
      (Coding.HammingWeight (l1CoefficientMap a + allOnes) : Int) (-1) (by
        simpa using l1_plus_allOnes_weight_cast8 a)
    calc
      OneQubitMagic.phaseAmplitude
          ((Coding.HammingWeight (l1CoefficientMap a + allOnes) : Real) *
            (Real.pi / 4)) =
        OneQubitMagic.phaseAmplitude
          (Real.pi / 4 *
            ((Coding.HammingWeight (l1CoefficientMap a + allOnes) : Int) : Real)) := by
              congr 1
              push_cast
              ring
      _ = OneQubitMagic.phaseAmplitude
          (Real.pi / 4 * ((-1 : Int) : Real)) := hphase
      _ = OneQubitMagic.phaseAmplitude (-Real.pi / 4) := by
        congr 1
        norm_num
        ring
theorem inv_sqrt_two_pow_fifteen_QECertEndpoint :
    (Real.sqrt 2 : Complex)⁻¹ ^ 15 =
      (32 : Complex)⁻¹ *
        ((4 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) := by
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast OneQubitMagic.sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast OneQubitMagic.sqrt_two_mul_self
  field_simp [hsqrt_ne]
  calc
    (32 : Complex) * 4 = 128 := by norm_num
    _ = (Real.sqrt 2 : Complex) ^ 14 := by
      symm
      calc
        (Real.sqrt 2 : Complex) ^ 14 =
            ((Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex)) ^ 7 := by ring
        _ = 128 := by rw [hsqrt_sq]; norm_num
theorem l2Syndrome_eq_zero_of_mem_rowCode_doubleDual_QECertEndpoint
    {word : Word} (hword : word ∈
      bk15CSSRows.rowCode.dual.dual.carrier) :
    l2Syndrome word = 0 := by
  funext check
  change Coding.wordPairing word (l2Generator check) = 0
  exact bk15CSSRows.rowCode.dual.orthogonal_of_mem_dual hword
    (l2Generator_mem_cssRowCodeDual check)
theorem mem_rowCode_doubleDual_of_mem_L2_dual_QECertEndpoint
    {word : Word} (hword : word ∈ L2.dual.carrier) :
    word ∈ bk15CSSRows.rowCode.dual.dual.carrier := by
  obtain ⟨a, c, rfl⟩ :=
    (mem_l2_dual_iff_exists_l1_plus_allOnes word).1 hword
  have hl1Even : l1CoefficientMap a ∈ bk15CSSRows.evenCode.carrier := by
    rw [bk15_evenCode_eq_L1]
    exact ⟨a, rfl⟩
  have hl1Row : l1CoefficientMap a ∈ bk15CSSRows.rowCode.carrier := by
    rw [bk15CSSRows.rowCode_eq_evenCode_sup_oddCode]
    exact Submodule.mem_sup_left hl1Even
  have hallRow : allOnes ∈ bk15CSSRows.rowCode.carrier := by
    change bk15CSSRows.oddRow () ∈ bk15CSSRows.rowCode.carrier
    exact bk15CSSRows.row_mem_rowCode (.inl ())
  have hrow : l1CoefficientMap a + c • allOnes ∈
      bk15CSSRows.rowCode.carrier :=
    bk15CSSRows.rowCode.carrier.add_mem hl1Row
      (bk15CSSRows.rowCode.carrier.smul_mem c hallRow)
  refine (bk15CSSRows.rowCode.dual.mem_dual _).2 ?_
  intro dualWord hdualWord
  exact bk15CSSRows.rowCode.dual_orthogonal hrow hdualWord

end Recurrence
end BK15
end Distillation
end QEC
end
end


