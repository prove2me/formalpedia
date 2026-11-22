-- Prove2me | Definitions.Def_BB5_Skelet26
-- name    : BB5_Skelet26
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:53:00.36623+00:00
-- url     : https://prove2.me/theorems/769db69b-ac8d-4e22-b275-17d6e4e173e3
-- title:
--   Skelet #26 (Shift Overflow Counter) (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #26 (Shift Overflow Counter) of the source paper, given in TNF linear form `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Two independent binary counters; the reset invariant maintained during each reset phase forbids the overflow that would cause a halt.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #26 (Shift Overflow Counter) of arXiv:2509.12337,
given in TNF linear form `1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---` (Figure 15 / Section 5 - Shift Overflow Counters). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet26 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, false, some 3)    -- A,1 -> 1LD
    | 1, false => (true, true, some 2)    -- B,0 -> 1RC
    | 1, true => (false, true, some 1)    -- B,1 -> 0RB
    | 2, false => (true, false, some 0)    -- C,0 -> 1LA
    | 2, true => (true, true, some 2)    -- C,1 -> 1RC
    | 3, false => (true, false, some 4)    -- D,0 -> 1LE
    | 3, true => (false, false, some 0)    -- D,1 -> 0LA
    | 4, false => (true, false, some 2)    -- E,0 -> 1LC
    | 4, true => (false, false, none)    -- E,1 -> ---

end BB5


