-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T17:35:21.696611+00:00
-- url     : https://prove2.me/theorems/5c23a7df-f8b4-4dfd-bd4e-34ed1da31850
-- title:
--   Decoded Error Bridge
-- statement:
--   Definitions and structural lemmas for Decoded Error Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/DecodedErrorBridge.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DecodedErrorSupport
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_NormalizedRun
import Theorems.Thm_QEC_Distillation_HH18Parameterized_errorBranchState_normSq

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
universe u v w
attribute [local instance 100] Fintype.ofFinite
local instance instDecodedBridgeClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
attribute [local instance] QEC.Distillation.HH18Parameterized.instDecodedBridgeClassicalDecidable
noncomputable def decodedErrorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) : DensityOperator (LogicalRegister m w) :=
  (decoderChannel h).mapDensity
    (DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error))
noncomputable def acceptedResidualDecodedDifference {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Operator (LogicalRegister m w) :=
  (physicalErrorWords m w).sum (fun error =>
    if Accepts w r m error ∧ error ≠ 0 then
      (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
        (decoderChannel h (errorBranchOperator h hdegree error) -
          (idealLogicalTOutput m w).toOperator)
    else 0)
end HH18Parameterized
end Distillation
end QEC


