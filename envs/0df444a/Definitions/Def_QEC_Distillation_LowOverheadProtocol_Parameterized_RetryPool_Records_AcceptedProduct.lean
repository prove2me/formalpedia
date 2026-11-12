-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:37:59.680675+00:00
-- url     : https://prove2.me/theorems/4ae3eda8-7656-4f37-ae27-57ed78f45f40
-- title:
--   Accepted Product
-- statement:
--   Definitions and structural lemmas for Accepted Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedProduct.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedInstrumentConditional
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Core
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
noncomputable def decodedRetryPoolAcceptedProductDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (required : Nat) :
    DensityOperator (QubitRegister (Fin required × LogicalSite m w)) :=
  tensorPowerRegisterProductDensity (LogicalSite m w)
    (resourceDecodedRun h hdegree
      (noisyResources m w epsilon)).acceptedOutput
    rhoUnit required
end HH18Parameterized
end Distillation
end QEC


