-- Prove2me | Definitions.Def_BB5_Skelet1
-- name    : BB5_Skelet1
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:46:28.209346+00:00
-- url     : https://prove2.me/theorems/42700baf-2874-452a-8443-e6472511a850
-- title:
--   Skelet #1 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #1 of the source paper, given in TNF linear form `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Translated Cycler: after ~5.42×10^51 steps of chaos it enters an infinite translated loop (period > 8 billion); proved non-halting by Kądziołka in busycoq (Skelet1.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Skelet #1 (Translated Cycler)

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #1 of arXiv:2509.12337,
given in TNF linear form `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC` (Figure 15 / Section 5 - Skelet #1 (Translated Cycler)). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet1 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, true, some 3)    -- A,1 -> 1RD
    | 1, false => (true, false, some 2)    -- B,0 -> 1LC
    | 1, true => (false, true, some 2)    -- B,1 -> 0RC
    | 2, false => (true, true, some 0)    -- C,0 -> 1RA
    | 2, true => (true, false, some 3)    -- C,1 -> 1LD
    | 3, false => (false, true, some 4)    -- D,0 -> 0RE
    | 3, true => (false, false, some 1)    -- D,1 -> 0LB
    | 4, false => (false, false, none)    -- E,0 -> ---
    | 4, true => (true, true, some 2)    -- E,1 -> 1RC

end BB5


