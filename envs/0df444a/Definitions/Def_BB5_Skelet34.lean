-- Prove2me | Definitions.Def_BB5_Skelet34
-- name    : BB5_Skelet34
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:54:44.733504+00:00
-- url     : https://prove2.me/theorems/6a60333b-5b54-4441-8736-753eb8063ee7
-- title:
--   Skelet #34 (Shift Overflow Counter) (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #34 (Shift Overflow Counter) of the source paper, given in TNF linear form `1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Two independent binary counters; first described informally by Ligocki, non-halting follows from the reset invariant.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #34 (Shift Overflow Counter) of arXiv:2509.12337,
given in TNF linear form `1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA` (Figure 15 / Section 5 - Shift Overflow Counters). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet34 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, false, some 2)    -- A,1 -> 1LC
    | 1, false => (false, true, some 2)    -- B,0 -> 0RC
    | 1, true => (false, true, some 1)    -- B,1 -> 0RB
    | 2, false => (true, false, some 3)    -- C,0 -> 1LD
    | 2, true => (false, false, some 0)    -- C,1 -> 0LA
    | 3, false => (true, false, some 4)    -- D,0 -> 1LE
    | 3, true => (false, false, none)    -- D,1 -> ---
    | 4, false => (true, false, some 0)    -- E,0 -> 1LA
    | 4, true => (true, true, some 0)    -- E,1 -> 1RA

end BB5


