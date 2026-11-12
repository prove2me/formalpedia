-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T19:26:01.520665+00:00
-- url     : https://prove2.me/theorems/b3bba202-aca9-4f83-8e2c-2a668241aef0
-- title:
--   Measured Record Product
-- statement:
--   Definitions and structural lemmas for Measured Record Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/MeasuredRecordProduct.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Mathlib.Analysis.InnerProductSpace.Dual
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
attribute [local instance 100] Fintype.ofFinite
def decodedRetryPoolDiagonalErrorRate
    (parameter : ErrorParameter) (hhalf : parameter.rate ≤ 1 / 2) :
    HH18NoisyInput.DiagonalErrorRate :=
  ⟨parameter.rate,
    parameter.rate_nonneg,
    hhalf⟩
noncomputable def decodedRetryPoolPhysicalRecordProductDensity
    (m w : Nat) (parameter : ErrorParameter)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (PhysicalRegister m w) :=
  (decodedRetryPoolQubitTensorPowerRegisterTransport (PhysicalSite m w)).conjDensity
    (tensorPowerProductInput
      (decodedRetryPoolOneQubitRecordDensity parameter)
      rhoUnit (Fintype.card (PhysicalSite m w)))
end HH18Parameterized
end Distillation
end QEC


