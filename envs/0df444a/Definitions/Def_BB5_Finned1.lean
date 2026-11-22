-- Prove2me | Definitions.Def_BB5_Finned1
-- name    : BB5_Finned1
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:56:31.6563+00:00
-- url     : https://prove2.me/theorems/8df54e5a-4f20-4b78-8bd4-c911169e4ce1
-- title:
--   Finned #1 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Finned #1 of the source paper, given in TNF linear form `1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Holds three unary numbers on the tape, merging the middle into a neighbour while preserving a linear relation; any deviation would halt, so it never halts.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Finned #1 of arXiv:2509.12337,
given in TNF linear form `1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA` (Figure 15 / Section 5 - Finned Machines). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def finned1 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (false, false, some 4)    -- A,1 -> 0LE
    | 1, false => (true, true, some 2)    -- B,0 -> 1RC
    | 1, true => (true, true, some 1)    -- B,1 -> 1RB
    | 2, false => (true, true, some 3)    -- C,0 -> 1RD
    | 2, true => (true, false, some 2)    -- C,1 -> 1LC
    | 3, false => (false, false, some 4)    -- D,0 -> 0LE
    | 3, true => (false, true, some 1)    -- D,1 -> 0RB
    | 4, false => (false, false, none)    -- E,0 -> ---
    | 4, true => (true, false, some 0)    -- E,1 -> 1LA

end BB5


