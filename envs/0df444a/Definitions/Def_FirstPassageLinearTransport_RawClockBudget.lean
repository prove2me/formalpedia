-- Prove2me | Definitions.Def_FirstPassageLinearTransport_RawClockBudget
-- name    : FirstPassageLinearTransport_RawClockBudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:16:55.984192+00:00
-- url     : https://prove2.me/theorems/58471523-12f4-5e16-9b48-24578086b8f7
-- title:
--   Raw Clock Budget
-- statement:
--   Definitions and structural lemmas for Raw Clock Budget, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def rawClockLeading (r eta : ℝ) : ℝ :=
  (3 / (2 * Real.log 2) + eta / Real.log 3) / (1 - r)
end
end FirstPassageLinearTransport


