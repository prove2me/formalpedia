-- Prove2me | Definitions.Def_BB5_Skelet10
-- name    : BB5_Skelet10
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:47:24.264816+00:00
-- url     : https://prove2.me/theorems/db582ff8-a0f0-4d9d-9bce-1fee6f6a0f56
-- title:
--   Skelet #10 (Double Fibonacci Counter) (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #10 (Double Fibonacci Counter) of the source paper, given in TNF linear form `1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Implements two independent base-Fibonacci counters (Zeckendorf representation); it halts iff the counters ever desynchronise, which never happens.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Skelet #10

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #10 (Double Fibonacci Counter) of arXiv:2509.12337,
given in TNF linear form `1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB` (Figure 15 / Section 5 - Skelet #10). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet10 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (false, true, some 0)    -- A,1 -> 0RA
    | 1, false => (false, false, some 2)    -- B,0 -> 0LC
    | 1, true => (true, true, some 0)    -- B,1 -> 1RA
    | 2, false => (true, true, some 4)    -- C,0 -> 1RE
    | 2, true => (true, false, some 3)    -- C,1 -> 1LD
    | 3, false => (true, false, some 2)    -- D,0 -> 1LC
    | 3, true => (false, false, some 3)    -- D,1 -> 0LD
    | 4, false => (false, false, none)    -- E,0 -> ---
    | 4, true => (false, true, some 1)    -- E,1 -> 0RB

end BB5


