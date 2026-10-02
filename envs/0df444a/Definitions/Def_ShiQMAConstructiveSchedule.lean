-- Prove2me | Definitions.Def_ShiQMAConstructiveSchedule
-- name    : ShiQMAConstructiveSchedule
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-01T12:54:06.099133+00:00
-- url     : https://prove2.me/theorems/1565c2b5-4486-43ed-a5d4-1d15ba5d5a1d
-- title:
--   Constructive logarithmic QMA amplification schedule
-- statement:
--   Defines the explicit logarithmic exponent budget and corresponding majority-repetition round count for a natural-coefficient target polynomial.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/24620b5/proofs/AMPUNI-constructive-schedule.lean#L10-L17

import Mathlib.Tactic
import Definitions.Def_ShiQMAErrorIteration

set_option autoImplicit false

namespace ShiQMAConstructiveSchedule

def exponentBudget (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  Nat.log 2 (p.eval 1 + 1) + 1 +
    p.natDegree * (Nat.log 2 (n + 1) + 1)

def rounds (p : Polynomial ℕ) (n : ℕ) : ℕ :=
  exponentBudget p n + 3

end ShiQMAConstructiveSchedule


