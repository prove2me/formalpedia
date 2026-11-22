-- Prove2me | Definitions.Def_BB5_Finned3
-- name    : BB5_Finned3
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:58:10.598651+00:00
-- url     : https://prove2.me/theorems/c3e029fc-b3b0-4cde-a0c9-a318f7b05654
-- title:
--   Finned #3 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Finned #3 of the source paper, given in TNF linear form `1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Holds three unary numbers maintaining a linear relation; also known to be irregular. Non-halting certified in busycoq (Finned3.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Finned #3 of arXiv:2509.12337,
given in TNF linear form `1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA` (Figure 15 / Section 5 - Finned Machines). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def finned3 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, true, some 4)    -- A,1 -> 1RE
    | 1, false => (true, false, some 2)    -- B,0 -> 1LC
    | 1, true => (true, true, some 1)    -- B,1 -> 1RB
    | 2, false => (false, true, some 0)    -- C,0 -> 0RA
    | 2, true => (false, false, some 3)    -- C,1 -> 0LD
    | 3, false => (true, false, some 1)    -- D,0 -> 1LB
    | 3, true => (true, false, some 3)    -- D,1 -> 1LD
    | 4, false => (false, false, none)    -- E,0 -> ---
    | 4, true => (false, true, some 0)    -- E,1 -> 0RA

end BB5


