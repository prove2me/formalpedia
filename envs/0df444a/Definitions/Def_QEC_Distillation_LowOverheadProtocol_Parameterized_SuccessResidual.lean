-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_SuccessResidual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T16:57:37.182571+00:00
-- url     : https://prove2.me/theorems/bc1eba4e-e958-429c-815b-0458807b657e
-- title:
--   Success Residual
-- statement:
--   Definitions and structural lemmas for Success Residual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SuccessResidual.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PhysicalEndpoint
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
attribute [local instance 100] Fintype.ofFinite
local instance instSuccessClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
noncomputable def rawAcceptedResidualErrorMass (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  (physicalErrorWords m w).sum (fun error =>
    if Accepts w r m error ∧ error ≠ 0 then
      HH18NoisyInput.errorWordWeight epsilon error
    else 0)
noncomputable def acceptedResidualError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  rawAcceptedResidualErrorMass w r m epsilon /
    endpointWeight h hdegree (noisyResources m w epsilon) .accepted
noncomputable def residualCoefficient (w _r m : Nat) : ℝ :=
  (Fintype.card (PhysicalErrorWord m w) : ℝ) /
    (1 / 2 : ℝ) ^ physicalInputCount m w
end HH18Parameterized
end Distillation
end QEC


