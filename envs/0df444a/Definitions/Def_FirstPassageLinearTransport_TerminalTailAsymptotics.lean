-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
-- name    : FirstPassageLinearTransport_TerminalTailAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:19:41.132834+00:00
-- url     : https://prove2.me/theorems/b7aaad89-3170-43d2-962a-869f3ac4599b
-- title:
--   Terminal Tail Asymptotics
-- statement:
--   Definitions and structural lemmas for Terminal Tail Asymptotics, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTailAsymptotics.lean

import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def terminalTailPrefactor (b b' c' : ℝ) : ℝ :=
  weightedTailConstant (Real.log 2) c' +
    Real.exp b * weightedTailConstant b b'
end
end FirstPassageLinearTransport


