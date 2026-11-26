-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeSupportScalars
-- name    : FirstPassageLinearTransport_TimeSupportScalars
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:20:50.913822+00:00
-- url     : https://prove2.me/theorems/da3d71d8-888f-480d-b94c-1e81d9adfb2f
-- title:
--   Time Support Scalars
-- statement:
--   Definitions and structural lemmas for Time Support Scalars, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportScalars.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def movingTimeSupportConstant
    (P : ShrinkingBarrierRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (C + 5) ^ 2)
end
end FirstPassageLinearTransport


