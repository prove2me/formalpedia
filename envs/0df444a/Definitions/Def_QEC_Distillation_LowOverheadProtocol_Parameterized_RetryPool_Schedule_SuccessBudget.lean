-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:36:51.571226+00:00
-- url     : https://prove2.me/theorems/bf094ac1-fe27-4e40-93fd-f643e6a305c3
-- title:
--   Success Budget
-- statement:
--   Definitions and structural lemmas for Success Budget, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
def decodedRetryPoolInitialPoolingDomain (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Prop :=
  routedDepthIterationScale w r m * epsilon.1 <=
    1 / (64 * (logicalOutputCount m w : Real))
noncomputable def decodedRetryPoolStageAggregateShortageBudget
    (w r m : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (stage : Nat) : Real :=
  (logicalOutputCount m w : Real) ^ stage *
    decodedRetryPoolDyadicDenominator stage *
    physicalInputCount m w *
    routedDepthErrorEnvelope w r m epsilon stage
end HH18Parameterized
end Distillation
end QEC


