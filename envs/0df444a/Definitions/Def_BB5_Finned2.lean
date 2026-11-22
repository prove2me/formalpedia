-- Prove2me | Definitions.Def_BB5_Finned2
-- name    : BB5_Finned2
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:57:24.546809+00:00
-- url     : https://prove2.me/theorems/c12726db-b5ef-412e-9c9c-77d1daf38b9e
-- title:
--   Finned #2 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Finned #2 of the source paper, given in TNF linear form `1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. Holds three unary numbers while maintaining a linear relation; non-halting certified by a hand-crafted WFAR-like certificate (Blanchard / Kądziołka, busycoq Finned2.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Finned #2 of arXiv:2509.12337,
given in TNF linear form `1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD` (Figure 15 / Section 5 - Finned Machines). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def finned2 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (true, true, some 0)    -- A,1 -> 1RA
    | 1, false => (true, true, some 2)    -- B,0 -> 1RC
    | 1, true => (true, false, some 1)    -- B,1 -> 1LB
    | 2, false => (false, false, some 3)    -- C,0 -> 0LD
    | 2, true => (false, true, some 0)    -- C,1 -> 0RA
    | 3, false => (true, true, some 0)    -- D,0 -> 1RA
    | 3, true => (true, false, some 4)    -- D,1 -> 1LE
    | 4, false => (false, false, none)    -- E,0 -> ---
    | 4, true => (false, false, some 3)    -- E,1 -> 0LD

end BB5


