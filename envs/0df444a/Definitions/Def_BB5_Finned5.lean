-- Prove2me | Definitions.Def_BB5_Finned5
-- name    : BB5_Finned5
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T14:01:35.074813+00:00
-- url     : https://prove2.me/theorems/12a1d49d-1451-49dc-8278-2c07c53d13be
-- title:
--   Finned #5 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Finned #5 of the source paper, given in TNF linear form `1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Holds three unary numbers while maintaining a linear relation; non-halting certified by a hand-crafted certificate (busycoq Finned5.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Finned #5 of arXiv:2509.12337,
given in TNF linear form `1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE` (Figure 15 / Section 5 - Finned Machines). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def finned5 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, false, some 0)    -- A,1 -> 1LA
    | 1, false => (false, false, some 2)    -- B,0 -> 0LC
    | 1, true => (false, true, some 4)    -- B,1 -> 0RE
    | 2, false => (false, false, none)    -- C,0 -> ---
    | 2, true => (true, false, some 3)    -- C,1 -> 1LD
    | 3, false => (true, false, some 0)    -- D,0 -> 1LA
    | 3, true => (false, false, some 2)    -- D,1 -> 0LC
    | 4, false => (true, true, some 0)    -- E,0 -> 1RA
    | 4, true => (true, true, some 4)    -- E,1 -> 1RE

end BB5


