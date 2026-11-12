-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
-- name    : QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:22:47.246195+00:00
-- url     : https://prove2.me/theorems/d73008c2-be97-4601-a455-6a8f098fe49b
-- title:
--   Decoded Error Bridge
-- statement:
--   Definitions and structural lemmas for Decoded Error Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/DecodedErrorBridge.lean

import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Decoder
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NormalizedRun
import Theorems.Thm_QEC_Distillation_HH18Protocol_errorBranchState_normSq

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
local instance instDecodedBridgeClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Protocol.instDecodedBridgeClassicalDecidable
noncomputable def decodedErrorBranch (error : PhysicalErrorWord) :
    DensityOperator LogicalRegister :=
  decoderChannel.mapDensity
    (DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error))
noncomputable def acceptedResidualDecodedDifference
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Operator LogicalRegister :=
  physicalErrorWords.sum (fun error =>
    if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
      (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
        (decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) -
          idealLogicalTOutput.toOperator)
    else 0)
end HH18Protocol
end Distillation
end QEC


