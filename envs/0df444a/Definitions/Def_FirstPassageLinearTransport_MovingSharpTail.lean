-- Prove2me | Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
-- name    : FirstPassageLinearTransport_MovingSharpTail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:18:07.469858+00:00
-- url     : https://prove2.me/theorems/8d853cbe-9605-4676-b605-fa8905fc27dc
-- title:
--   Moving Sharp Tail
-- statement:
--   Definitions and structural lemmas for Moving Sharp Tail, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
def exactSharpCriticalLowSeriesConstant (b₀ Cpref : ℝ) : ℝ :=
  max
    (weightedTailConstant (Real.log 2) (Real.log 2 / 2))
    (3 * Cpref * weightedTailConstant b₀ (b₀ / 2)) + 1
end
end FirstPassageLinearTransport


