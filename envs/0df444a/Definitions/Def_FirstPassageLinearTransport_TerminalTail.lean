-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TerminalTail
-- name    : FirstPassageLinearTransport_TerminalTail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:07:18.181343+00:00
-- url     : https://prove2.me/theorems/f0ba136f-a31b-539d-8ecd-1690175e4448
-- title:
--   Terminal Tail
-- statement:
--   Definitions and structural lemmas for Terminal Tail, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalTail.lean

import Mathlib.Algebra.Order.Field.GeomSum
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def weightedTailConstant (c c' : ℝ) : ℝ :=
  (1 + 1 / (c - c')) / (1 - Real.exp (-c'))
end
end FirstPassageLinearTransport


