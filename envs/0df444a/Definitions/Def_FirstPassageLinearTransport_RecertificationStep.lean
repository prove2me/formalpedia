-- Prove2me | Definitions.Def_FirstPassageLinearTransport_RecertificationStep
-- name    : FirstPassageLinearTransport_RecertificationStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:05:52.589345+00:00
-- url     : https://prove2.me/theorems/81729bd2-3e97-5c98-9e1e-ddbf8d01e1d7
-- title:
--   Recertification Step
-- statement:
--   Definitions and structural lemmas for Recertification Step, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationStep.lean

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
def rationalTargetRank (r : ℚ) (m : ℕ) : ℕ :=
  ⌊(r : ℝ) * (m : ℝ)⌋₊
end
end FirstPassageLinearTransport


