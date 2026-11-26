-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
-- name    : FirstPassageLinearTransport_ShrinkingSchedules
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:12:56.044168+00:00
-- url     : https://prove2.me/theorems/61885687-303c-414f-8aa6-139c6cb3b7e4
-- title:
--   Shrinking Schedules
-- statement:
--   Definitions and structural lemmas for Shrinking Schedules, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingSchedules.lean

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def shrinkingSwitchRank (C : ℝ) (M : ℕ) : ℕ :=
  ⌈C * Real.log ((M : ℝ) + 2)⌉₊
def shrinkingTimeSupportConstant
    (P : ShrinkingBarrierRunData) (C : ℝ) : ℝ :=
  2 + 2 / driftGap *
    ((P.D + P.tau + 3) / (1 - Real.sqrt (P.rHi : ℝ)) +
      (2 * P.etaLo + 3) * (C + 1) / (1 - (P.rLo : ℝ)))
end
end FirstPassageLinearTransport


