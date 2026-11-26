-- Prove2me | Definitions.Def_UntimedEndpointExchange
-- name    : UntimedEndpointExchange
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T21:55:52.846269+00:00
-- url     : https://prove2.me/theorems/e6f9a7d2-7870-4c87-bce8-95b5b122144f
-- title:
--   Sequences of crossing destinations without timestamps
-- statement:
--   Given a deterministic transition system, a Boolean side label on states, a start state, and a finite step count, record each state entered when the side changes. The record retains these destination states in order and leaves out the elapsed time of each crossing.
-- source:
--   Crossing-sequence method. See F. C. Hennie, One-tape, off-line Turing machine computations, 1965, DOI 10.1016/S0019-9958(65)90399-2.

import Mathlib

set_option autoImplicit false

namespace UntimedCrossings

/-- The destination states of all completed crossings, in their original order. -/
def untimedRecord {S : Type*} (side : S → Bool) (step : S → S) (z : S) : ℕ → List S
  | 0 => []
  | T+1 =>
    if side (step z) ≠ side z then step z :: untimedRecord side step (step z) T
    else untimedRecord side step (step z) T

end UntimedCrossings


