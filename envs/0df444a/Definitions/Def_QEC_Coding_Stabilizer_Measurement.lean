-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Measurement
-- name    : QEC_Coding_Stabilizer_Measurement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:27:30.996204+00:00
-- url     : https://prove2.me/theorems/ddcf59cd-a68f-4e61-bdf7-94b8aabada1a
-- title:
--   Measurement
-- statement:
--   Definitions and structural lemmas for Measurement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
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
namespace QEC
namespace Coding
namespace PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
inductive StabilizerOutcome
  | positive
  | negative
deriving DecidableEq
instance : Fintype StabilizerOutcome where
  elems := {.positive, .negative}
  complete outcome := by cases outcome <;> simp
namespace StabilizerOutcome
def sign : StabilizerOutcome → Complex
  | .positive => 1
  | .negative => -1
def opposite : StabilizerOutcome → StabilizerOutcome
  | .positive => .negative
  | .negative => .positive
@[simp]
theorem sign_opposite (outcome : StabilizerOutcome) :
    outcome.opposite.sign = -outcome.sign := by
  cases outcome <;> norm_num [opposite, sign]
@[simp]
theorem opposite_opposite (outcome : StabilizerOutcome) :
    outcome.opposite.opposite = outcome := by
  cases outcome <;> rfl
@[simp]
theorem sign_mul_self (outcome : StabilizerOutcome) :
    outcome.sign * outcome.sign = 1 := by
  cases outcome <;> norm_num [sign]
end StabilizerOutcome
def stabilizerProjector (P : Binary ι) (outcome : StabilizerOutcome) :
    Operator (Qubit.QubitRegister ι) :=
  (1 / 2 : Complex) •
    (1 + outcome.sign • toHermitianQubitOperator P)
theorem stabilizerProjector_adjoint
    (P : Binary ι) (outcome : StabilizerOutcome) :
    LinearMap.adjoint (stabilizerProjector P outcome) =
      stabilizerProjector P outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold stabilizerProjector
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
        exact adjoint_toHermitianQubitOperator_eq_self P
theorem stabilizerProjector_idempotent
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome * stabilizerProjector P outcome =
      stabilizerProjector P outcome := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      toHermitianQubitOperator_square] <;>
    module
theorem stabilizerProjector_add_opposite
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome +
        stabilizerProjector P outcome.opposite = 1 := by
  cases outcome <;>
    simp only [stabilizerProjector, StabilizerOutcome.sign,
      StabilizerOutcome.opposite] <;>
    module
def stabilizerKrausFamily (P : Binary ι) :
    FiniteKrausFamily StabilizerOutcome
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  operator := stabilizerProjector P
@[simp]
theorem stabilizerKrausFamily_operator
    (P : Binary ι) (outcome : StabilizerOutcome) :
    (stabilizerKrausFamily P).operator outcome =
      stabilizerProjector P outcome :=
  rfl
theorem stabilizerKrausFamily_complete (P : Binary ι) :
    (stabilizerKrausFamily P).Complete := by
  classical
  unfold FiniteKrausFamily.Complete
  simp only [stabilizerKrausFamily_operator, stabilizerProjector_adjoint]
  change
    (∑ outcome : StabilizerOutcome,
      stabilizerProjector P outcome * stabilizerProjector P outcome) = 1
  rw [show (Finset.univ : Finset StabilizerOutcome) =
      {.positive, .negative} by decide]
  simpa [stabilizerProjector_idempotent, StabilizerOutcome.opposite] using
    stabilizerProjector_add_opposite P .positive
def stabilizerInstrument (P : Binary ι) :
    FiniteInstrument StabilizerOutcome StabilizerOutcome
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  kraus := stabilizerKrausFamily P
  observe := fun outcome => outcome
def stabilizerConditionalDensity
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (stabilizerInstrument P).bornWeight outcome rho) :
    DensityOperator (Qubit.QubitRegister ι) :=
  (stabilizerInstrument P).conditionalDensity outcome rho hpos
end PauliSymplectic
end Coding
end QEC


