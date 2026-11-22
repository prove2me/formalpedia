-- Prove2me | Definitions.Def_BB5_winner
-- name    : BB5_winner
-- status  : Definition
-- author  : @loader3229
-- created : 2026-11-21T16:05:35.217244+00:00
-- url     : https://prove2.me/theorems/ea23bd6b-4b29-41aa-9214-ce0ae796046a
-- title:
--   5-state Busy Beaver winner (Figure 1)
-- statement:
--   The concrete 5-state, 2-symbol Turing machine discovered by Marxen and Buntrock in 1989, given in the paper as `1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA`. It halts after 47,176,870 steps from the all-zero tape and is the champion witnessing the lower bound on $S(5)$. States $A$–$E$ are encoded as $0$–$4$, symbol $0$ as `false` and $1$ as `true`, moves Right/Left as `true`/`false`, and an undefined (halting) transition as `none`.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Figure 1(a)

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- The 5-state 2-symbol Busy Beaver winner discovered by Marxen and Buntrock (1989),
given in linear form `1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA` (paper Figure 1(a)).
States A,B,C,D,E are encoded as 0,1,2,3,4; symbol `false` is 0 and `true` is 1;
a move direction `true` is Right and `false` is Left; `none` is an undefined
transition, i.e. the machine halts. -/
def winner : FCP.BusyBeaver.TM 5 where
  trans
    | 0, false => (true, true, some 1)    -- A,0 -> 1 R B
    | 0, true  => (true, false, some 2)   -- A,1 -> 1 L C
    | 1, false => (true, true, some 2)    -- B,0 -> 1 R C
    | 1, true  => (true, true, some 1)    -- B,1 -> 1 R B
    | 2, false => (true, true, some 3)    -- C,0 -> 1 R D
    | 2, true  => (false, false, some 4)  -- C,1 -> 0 L E
    | 3, false => (true, false, some 0)   -- D,0 -> 1 L A
    | 3, true  => (true, false, some 3)   -- D,1 -> 1 L D
    | 4, false => (false, false, none)    -- E,0 -> --- (halt)
    | 4, true  => (false, false, some 0)  -- E,1 -> 0 L A

end BB5


