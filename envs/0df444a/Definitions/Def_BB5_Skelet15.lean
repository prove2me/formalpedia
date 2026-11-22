-- Prove2me | Definitions.Def_BB5_Skelet15
-- name    : BB5_Skelet15
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:52:00.453342+00:00
-- url     : https://prove2.me/theorems/a8671143-1288-403c-9f57-8e8043432566
-- title:
--   Skelet #15 (Shift Overflow Counter) (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #15 (Shift Overflow Counter) of the source paper, given in TNF linear form `1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Two independent binary counters (left and right). An orderly counter phase alternates with a reset phase; the reset invariant prevents a second overflow, so it never halts.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #15 (Shift Overflow Counter) of arXiv:2509.12337,
given in TNF linear form `1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC` (Figure 15 / Section 5 - Shift Overflow Counters). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet15 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (false, false, none)    -- A,1 -> ---
    | 1, false => (true, true, some 2)    -- B,0 -> 1RC
    | 1, true => (true, false, some 1)    -- B,1 -> 1LB
    | 2, false => (true, false, some 3)    -- C,0 -> 1LD
    | 2, true => (true, true, some 4)    -- C,1 -> 1RE
    | 3, false => (true, false, some 1)    -- D,0 -> 1LB
    | 3, true => (false, false, some 3)    -- D,1 -> 0LD
    | 4, false => (true, true, some 0)    -- E,0 -> 1RA
    | 4, true => (false, true, some 2)    -- E,1 -> 0RC

end BB5


