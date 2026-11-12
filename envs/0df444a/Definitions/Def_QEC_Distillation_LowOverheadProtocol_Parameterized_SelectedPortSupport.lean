-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:27:44.782417+00:00
-- url     : https://prove2.me/theorems/a613ddad-bb15-4d58-a6ba-0f858a205582
-- title:
--   Selected Port Support
-- statement:
--   Definitions and structural lemmas for Selected Port Support, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPortSupport.lean

import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitABasisSupport
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
noncomputable def aBasisProjectorProbability
    (outcome : StabilizerOutcome) (rho : DensityOperator QubitSpace) : ℝ :=
  (LinearMap.trace Complex QubitSpace
    (aBasisProjector outcome * rho.toOperator)).re
end OneQubitABasisSupport
end Distillation
end QEC


