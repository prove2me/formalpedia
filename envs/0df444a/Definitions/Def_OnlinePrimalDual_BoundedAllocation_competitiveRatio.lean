-- Prove2me | Definitions.Def_OnlinePrimalDual_BoundedAllocation_competitiveRatio
-- name    : OnlinePrimalDual_BoundedAllocation_competitiveRatio
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:02:24.436872+00:00
-- url     : https://prove2.me/theorems/f637ad51-d2e3-41f9-b15f-e7b8da6d73f1
-- title:
--   The allocation algorithm's competitive ratio C(d)
-- statement:
--   `competitiveRatio d := C(d) = 1 - (d-1)/(d(1+1/(d-1))^(d-1))`, the book's own closed form,
--   taken verbatim (Theorem 13.1, p. 240).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 240, Theorem 13.1

import Mathlib

namespace OnlinePrimalDual.BoundedAllocation

/-- The allocation algorithm's competitive ratio, `C(d) = 1 - (d-1)/(d(1+1/(d-1))^(d-1))`
(Buchbinder & Naor, FnT TCS 2009, Theorem 13.1, p. 240), taken verbatim from the book's own
closed form. -/
noncomputable def competitiveRatio (d : ℕ) : ℝ :=
  1 - ((d : ℝ) - 1) / ((d : ℝ) * (1 + 1 / ((d : ℝ) - 1)) ^ (d - 1))

end OnlinePrimalDual.BoundedAllocation


