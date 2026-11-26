-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
-- name    : FirstPassageLinearTransport_TimeoutRawClock
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:25:40.267426+00:00
-- url     : https://prove2.me/theorems/94c8f312-ff9f-5543-8578-a5f4ba355fde
-- title:
--   Timeout Raw Clock
-- statement:
--   Definitions and structural lemmas for Timeout Raw Clock, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def timeoutRawClockSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  let T := timeoutTimeSupportConstant P C
  T + (2 * driftGap / 3) *
    (driftGap / 2 * T + 2) * Real.log 2 / Real.log 3
def timeoutCompletedRawClockSupportConstant
    (P : TimeoutHighRunData) (C : ℝ) : ℝ :=
  timeoutRawClockSupportConstant P C + timeoutTimeSupportConstant P C
end
end FirstPassageLinearTransport


