-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T20:56:05.560859+00:00
-- url     : https://prove2.me/theorems/518481fb-f8b7-43f3-8ecc-9e7355ef6967
-- title:
--   Run
-- statement:
--   Definitions and structural lemmas for Run, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Run.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessLowerBound
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolInstrument_complete

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolTensorUnitDensity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] : DensityOperator (tensorPowerCarrier H 0) :=
  DensityOperator.pureDensity
    (tensorPowerBasis (stdOrthonormalBasis Complex H) 0 PUnit.unit) (by
      rw [show ‖tensorPowerBasis (stdOrthonormalBasis Complex H) 0 PUnit.unit‖ = 1 from
        (tensorPowerBasis (stdOrthonormalBasis Complex H) 0).norm_eq_one PUnit.unit]
      norm_num)
noncomputable def decodedRetryPoolPhysicalProtocolNoisyResources
    (m w z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    Fin (physicalInputCount m w *
      decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) →
      DensityOperator QubitSpace :=
  fun _ => HH18NoisyInput.noisyTInvResource epsilon
noncomputable def decodedRetryPoolPhysicalProtocolPrepareBlocks
    {m w : Nat}
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (attempts : Nat) →
    (Fin attempts → DensityOperator (PhysicalRegister m w)) →
      DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)
  | 0, _ => rhoUnit
  | attempts + 1, inputs =>
      DensityOperator.tensorDensity (inputs 0)
        (decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts
          (fun trial => inputs trial.succ))
noncomputable def decodedRetryPoolPhysicalProtocolPrepareResources
    (m w attempts : Nat)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (inputs : Fin (physicalInputCount m w * attempts) → DensityOperator QubitSpace) :
    DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts) :=
  decodedRetryPoolPhysicalProtocolPrepareBlocks rhoUnit attempts fun trial =>
    prepareMeasuredResources m w fun site =>
      inputs (finProdFinEquiv (site, trial))
def decodedRetryPoolNestedConstantHistory
    {alpha : Type*} (value : alpha) (branches : Nat) :
    (depth : Nat) → nestedTensorHistory alpha branches depth
  | 0 => value
  | depth + 1 =>
      decodedRetryPoolNestedConstantHistory
        (tensorPowerHistoryOf alpha branches (fun _ => value)) branches depth
def decodedRetryPoolPhysicalProtocolFallbackLabel
    (m w z q : Nat) (hz : 0 < z) :
    nestedTensorHistory
      (Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
      (logicalOutputCount m w) (z - 1) := by
  let zeroWord :
      Bitstring
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w) :=
    fun _ => 0
  exact decodedRetryPoolNestedConstantHistory zeroWord
    (logicalOutputCount m w) (z - 1)
noncomputable def decodedRetryPoolPhysicalProtocolFallback
    (m w z q : Nat) (hz : 0 < z) :
    DensityOperator (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) :=
  DensityOperator.pureDensity
    (nestedTensorBasis
      (EuclideanSpace.basisFun
        (Bitstring
          (Fin (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz)) × LogicalSite m w))
        Complex)
      (logicalOutputCount m w) (z - 1)
      (decodedRetryPoolPhysicalProtocolFallbackLabel m w z q hz)) (by
        rw [OrthonormalBasis.norm_eq_one]
        norm_num)
noncomputable def decodedRetryPoolPhysicalProtocolRun
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DistillationRun QubitSpace
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz)
      (decodedRetryPoolPhysicalProtocolOutputCarrier m w z q hz) :=
  binaryDistillationRun
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz)
    (physicalInputCount m w *
      decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
    (decodedRetryPoolPhysicalProtocolNoisyResources m w z q hz epsilon)
    (decodedRetryPoolPhysicalProtocolPrepareResources m w
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) rhoUnit)
    (decodedRetryPoolPhysicalProtocolFallback m w z q hz)
end HH18Parameterized
end Distillation
end QEC


