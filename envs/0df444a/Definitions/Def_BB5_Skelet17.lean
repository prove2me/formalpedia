-- Prove2me | Definitions.Def_BB5_Skelet17
-- name    : BB5_Skelet17
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-22T13:50:58.568773+00:00
-- url     : https://prove2.me/theorems/3886bbdd-8234-4820-b59b-7b08905591eb
-- title:
--   Skelet #17 (sporadic machine)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine Skelet #17 of the source paper, given in TNF linear form `1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA` (Figure 15, Section 5). States A-E are encoded as 0-4, symbol 0 as `false` and 1 as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`. The last 5-state machine to be proved non-halting. Manages a unary-encoded list of naturals evolving by Gray-code-like transformations; it would halt only if n1=n2=0 and n3..nk all even, which never occurs.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Skelet #17 (last solved machine)

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The sporadic (non-halting) 5-state machine Skelet #17 of arXiv:2509.12337,
given in TNF linear form `1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA` (Figure 15 / Section 5 - Skelet #17 (last solved machine)). States A-E are 0-4,
symbol 0 is `false` and 1 is `true`, move Right/Left is `true`/`false`, and
an undefined (`---`) transition is `none`. -/
def skelet17 : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1RB
    | 0, true => (false, false, none)    -- A,1 -> ---
    | 1, false => (false, false, some 2)    -- B,0 -> 0LC
    | 1, true => (true, true, some 4)    -- B,1 -> 1RE
    | 2, false => (false, false, some 3)    -- C,0 -> 0LD
    | 2, true => (true, false, some 2)    -- C,1 -> 1LC
    | 3, false => (true, true, some 0)    -- D,0 -> 1RA
    | 3, true => (true, false, some 1)    -- D,1 -> 1LB
    | 4, false => (false, true, some 1)    -- E,0 -> 0RB
    | 4, true => (false, true, some 0)    -- E,1 -> 0RA

end BB5


