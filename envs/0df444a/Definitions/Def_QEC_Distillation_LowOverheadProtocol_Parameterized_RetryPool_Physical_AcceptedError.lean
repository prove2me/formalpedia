-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T21:01:30.737762+00:00
-- url     : https://prove2.me/theorems/10adf446-9485-4355-8e25-44b1c430c34e
-- title:
--   Accepted Error
-- statement:
--   Definitions and structural lemmas for Accepted Error, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) : Real :=
  Complex.re (LinearMap.trace Complex QubitSpace
    (aBasisInstrument.branchOperator .negative
      ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
        m w z q hz coordinate)
        ((decodedRetryPoolPhysicalProtocolBinaryInstrument
          h hdegree z q hz).branchOperator .accepted rho.toOperator))))
end HH18Parameterized
end Distillation
end QEC


