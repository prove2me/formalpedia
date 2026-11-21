-- Prove2me | Definitions.Def_QEC_Distillation_BK15_NegativeAHistoryOperatorSupport_QECert
-- name    : QEC_Distillation_BK15_NegativeAHistoryOperatorSupport_QECert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:24:30.773189+00:00
-- url     : https://prove2.me/theorems/f45bfb16-572a-4f5c-947c-a004b34b2e24
-- title:
--   BK15 negative-A history operator support
-- statement:
--   Exact operator and encoding identities used by the BK15 negative-A history proof.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Recurrence.lean

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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


section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
private theorem jointStabilizerProjector_mul_factor
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
  classical
  let reduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check))
  have hfactor : reduced * jointStabilizerFactor checks syndrome check =
      jointStabilizerProjector checks hcomm syndrome := by
    simpa [reduced, jointStabilizerProjector] using
      (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
        (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))
  calc
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerFactor checks syndrome check =
        (reduced * jointStabilizerFactor checks syndrome check) *
          jointStabilizerFactor checks syndrome check := by rw [hfactor]
    _ = reduced *
        (jointStabilizerFactor checks syndrome check *
          jointStabilizerFactor checks syndrome check) := by rw [mul_assoc]
    _ = reduced * jointStabilizerFactor checks syndrome check := by
        rw [jointStabilizerFactor_idempotent]
    _ = jointStabilizerProjector checks hcomm syndrome := hfactor
private theorem jointStabilizerFactor_mul_jointStabilizerProjector
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerFactor checks syndrome check *
        jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome := by
  have hcommProduct : Commute (jointStabilizerFactor checks syndrome check)
      (jointStabilizerProjector checks hcomm syndrome) := by
    unfold jointStabilizerProjector
    exact Finset.noncommProd_commute Finset.univ
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
      (jointStabilizerFactor checks syndrome check)
      (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
  rw [hcommProduct.eq]
  exact jointStabilizerProjector_mul_factor checks hcomm syndrome check
private theorem jointStabilizerFactor_eigen
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator (checks check) *
        jointStabilizerFactor checks syndrome check =
      (syndrome check).sign • jointStabilizerFactor checks syndrome check := by
  unfold jointStabilizerFactor stabilizerProjector
  cases outcome : syndrome check <;>
    simp only [outcome, StabilizerOutcome.sign, smul_mul_assoc,
      mul_smul_comm, mul_add, mul_one, toHermitianQubitOperator_square] <;>
    module
end PauliSymplectic
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.QEC.Coding.PauliSymplectic.jointStabilizerProjector_eigen_QECertNegativeAHistorySupport
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator (checks check) *
        jointStabilizerProjector checks hcomm syndrome =
      (syndrome check).sign • jointStabilizerProjector checks hcomm syndrome := by
  let factor := jointStabilizerFactor checks syndrome check
  have hfactor : factor * jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
    jointStabilizerFactor_mul_jointStabilizerProjector checks hcomm syndrome check
  calc
    toHermitianQubitOperator (checks check) *
        jointStabilizerProjector checks hcomm syndrome =
      toHermitianQubitOperator (checks check) *
        (factor * jointStabilizerProjector checks hcomm syndrome) := by rw [hfactor]
    _ = (toHermitianQubitOperator (checks check) * factor) *
        jointStabilizerProjector checks hcomm syndrome := by rw [mul_assoc]
    _ = ((syndrome check).sign • factor) *
        jointStabilizerProjector checks hcomm syndrome := by
      rw [show toHermitianQubitOperator (checks check) * factor =
        (syndrome check).sign • factor by
          dsimp [factor]
          exact jointStabilizerFactor_eigen checks syndrome check]
    _ = (syndrome check).sign •
        (factor * jointStabilizerProjector checks hcomm syndrome) := by
      rw [smul_mul_assoc]
    _ = (syndrome check).sign • jointStabilizerProjector checks hcomm syndrome := by
      rw [hfactor]
end QEC.Coding.PauliSymplectic
end
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.QEC.Coding.PauliSymplectic.stabilizerProjector_mul_opposite_QECertNegativeAHistorySupport
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome *
        stabilizerProjector P outcome.opposite = 0 := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      StabilizerOutcome.opposite, smul_mul_assoc, mul_smul_comm,
      mul_add, add_mul, one_mul, mul_one,
      toHermitianQubitOperator_square] <;>
    module
end QEC.Coding.PauliSymplectic
end
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
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


section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
private theorem StabilizerOutcome.eq_opposite_of_ne
    (left right : StabilizerOutcome) (hne : left ≠ right) :
    right = left.opposite := by
  cases left <;> cases right <;>
    simp [StabilizerOutcome.opposite] at hne ⊢
private theorem jointStabilizerProjector_erase_mul
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    (Finset.univ.erase check).noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome (Finset.univ.erase check)) *
      jointStabilizerFactor checks syndrome check =
        jointStabilizerProjector checks hcomm syndrome := by
  classical
  simpa [jointStabilizerProjector] using
    (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
      (jointStabilizerFactor checks syndrome)
      (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ))
private theorem exists_check_of_jointSyndrome_ne
    (left right : JointSyndrome κ) (hne : left ≠ right) :
    ∃ check, left check ≠ right check := by
  classical
  by_contra hnone
  push_neg at hnone
  exact hne (funext hnone)
end PauliSymplectic
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.QEC.Coding.PauliSymplectic.jointStabilizerProjector_mul_of_ne_QECertNegativeAHistorySupport
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight = 0 := by
  classical
  obtain ⟨check, hcheck⟩ :=
    exists_check_of_jointSyndrome_ne syndromeLeft syndromeRight hne
  have hopposite : syndromeRight check = (syndromeLeft check).opposite :=
    StabilizerOutcome.eq_opposite_of_ne (syndromeLeft check) (syndromeRight check) hcheck
  let leftReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeLeft)
    (jointStabilizerFactor_pairwise checks hcomm syndromeLeft (Finset.univ.erase check))
  let rightReduced := (Finset.univ.erase check).noncommProd
    (jointStabilizerFactor checks syndromeRight)
    (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
  have hleftFactor : leftReduced * jointStabilizerFactor checks syndromeLeft check =
      jointStabilizerProjector checks hcomm syndromeLeft := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeLeft check
  have hrightFactor : rightReduced * jointStabilizerFactor checks syndromeRight check =
      jointStabilizerProjector checks hcomm syndromeRight := by
    exact jointStabilizerProjector_erase_mul checks hcomm syndromeRight check
  have hcross : Commute (jointStabilizerFactor checks syndromeLeft check) rightReduced := by
    dsimp [rightReduced]
    exact Finset.noncommProd_commute (Finset.univ.erase check)
      (jointStabilizerFactor checks syndromeRight)
      (jointStabilizerFactor_pairwise checks hcomm syndromeRight (Finset.univ.erase check))
      (jointStabilizerFactor checks syndromeLeft check)
      (fun other _ =>
        jointStabilizerFactor_commute checks hcomm check other syndromeLeft syndromeRight)
  have hsingle : jointStabilizerFactor checks syndromeLeft check *
      jointStabilizerFactor checks syndromeRight check = 0 := by
    change stabilizerProjector (checks check) (syndromeLeft check) *
        stabilizerProjector (checks check) (syndromeRight check) = 0
    rw [hopposite]
    exact stabilizerProjector_mul_opposite_QECertNegativeAHistorySupport (checks check) (syndromeLeft check)
  calc
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight =
        (leftReduced * jointStabilizerFactor checks syndromeLeft check) *
          (rightReduced * jointStabilizerFactor checks syndromeRight check) := by
            rw [hleftFactor, hrightFactor]
    _ = leftReduced *
        (jointStabilizerFactor checks syndromeLeft check * rightReduced) *
          jointStabilizerFactor checks syndromeRight check := by
            simp only [mul_assoc]
    _ = leftReduced *
        (rightReduced * jointStabilizerFactor checks syndromeLeft check) *
          jointStabilizerFactor checks syndromeRight check := by
            rw [hcross.eq]
    _ = (leftReduced * rightReduced) *
        (jointStabilizerFactor checks syndromeLeft check *
          jointStabilizerFactor checks syndromeRight check) := by
            simp only [mul_assoc]
    _ = 0 := by rw [hsingle, mul_zero]
end QEC.Coding.PauliSymplectic
end
end

section
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
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite
set_option maxRecDepth 65536
namespace QEC.Distillation.BK15.Protocol
theorem _root_.QEC.Distillation.BK15.Protocol.aWordCorrectionTransport_eigen_QECertNegativeAHistorySupport (word error : Word) :
    aWordCorrectionTransport word (bk15ErrorWordState error) =
      binaryPhaseScalar (word ⬝ᵥ error) • bk15ErrorWordState error := by
  simp [aWordCorrectionTransport, aWordCorrectionTensor, bk15ErrorWordState,
    bk15TensorErrorState, dotProduct,
    binaryPhaseScalar_sum, aBitTransport_aInputState]
  simp_rw [← TensorProduct.smul_tmul']
  simp_rw [TensorProduct.tmul_smul]
  simp_rw [map_smul]
  simp_rw [smul_smul]
  simp only [Fin.isValue, Fin.prod_univ_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
    Fin.default_eq_zero, Finset.prod_singleton]
  congr 1
  ring
end QEC.Distillation.BK15.Protocol
end
end

section

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.QEC.Semantics.FiniteKrausFamily.toQuantumChannel_apply_sum_QECertNegativeAHistorySupport (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) := by
  rw [toQuantumChannel_apply, inducedMap_apply]
end QEC.Semantics.FiniteKrausFamily
end
end

section
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
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Protocol
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput
open scoped BigOperators TensorProduct
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.BK15.Protocol
theorem _root_.QEC.Distillation.BK15.Protocol.decoderChannel_rankOne_encoded_QECertNegativeAHistorySupport (psi : LogicalRegister) :
    decoderChannel (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry psi) (ambientEncodingIsometry psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [decoderChannel, FiniteKrausFamily.toQuantumChannel_apply_sum_QECertNegativeAHistorySupport,
    Fintype.sum_sum_type]
  simp only [decoderKrausFamily]
  simp_rw [sandwich_rankOne]
  rw [Fintype.sum_unique]
  simp only [codeDecoderBranch_encoded]
  have hcomplement : ∀ i, complementDecoderBranch i (ambientEncodingIsometry psi) = 0 := by
    intro i
    have hinner : inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
        (ambientEncodingIsometry psi) = 0 := by
      rw [← LinearMap.adjoint_inner_right, decoderComplementProjector_adjoint,
        decoderComplementProjector_encoded]
      simp
    change inner Complex (decoderComplementProjector (decoderPhysicalBasis i))
      (ambientEncodingIsometry psi) • decoderFallbackState = 0
    rw [hinner]
    simp
  simp_rw [hcomplement]
  simp
end QEC.Distillation.BK15.Protocol
end
end

section
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.QEC.Distillation.OneQubitMagic.trace_mul_rankOne_QECertNegativeAHistorySupport
    (P : Operator QubitSpace) (u : QubitSpace) :
    LinearMap.trace Complex QubitSpace
      (P * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
      inner Complex u (P u) := by
  have hcomp :
      P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap =
        (InnerProductSpace.rankOne Complex (P u) u).toLinearMap := by
    ext z
    simp [LinearMap.comp_apply, InnerProductSpace.rankOne_apply]
  change LinearMap.trace Complex QubitSpace
      (P.comp (InnerProductSpace.rankOne Complex u u).toLinearMap) = _
  rw [hcomp, InnerProductSpace.trace_rankOne]
end QEC.Distillation.OneQubitMagic
end
end

section


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.QEC.Distillation.Triorthogonal.BinaryRowFamily.encoding_apply_of_mem_QECertNegativeAHistorySupport
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encoding hR psi : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar *
        psi ((R.logicalBasisEquivLogicalQuotient hR).symm
          (Submodule.Quotient.mk
            ⟨bitstringWordEquiv Col bits, hbits⟩)) := by
  change R.cssNormalizationScalar *
      PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister
        R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) bits = _
  rw [PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) hbits]
  rfl
end QEC.Distillation.Triorthogonal.BinaryRowFamily
end
end

section
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
namespace QEC.Distillation.Triorthogonal.BinaryRowFamily
theorem _root_.QEC.Distillation.Triorthogonal.BinaryRowFamily.encoding_apply_of_not_mem_QECertNegativeAHistorySupport
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (psi : Qubit.QubitRegister OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∉ R.rowCode.dual.dual.carrier) :
    (R.encoding hR psi : Qubit.QubitRegister Col) bits = 0 := by
  change R.cssNormalizationScalar *
      PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister
        R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) bits = 0
  rw [PauliSymplectic.binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    R.evenCode R.rowCode.dual (R.logicalBasisReindex hR psi) hbits]
  simp
end QEC.Distillation.Triorthogonal.BinaryRowFamily
end
end


