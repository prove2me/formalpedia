-- Prove2me | Definitions.Def_d9NextRevenue
-- name    : d9NextRevenue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T10:45:17.821466+00:00
-- url     : https://prove2.me/theorems/f6f24c1b-ebcd-42f2-92f6-3c45b5ea3032
-- title:
--   One-step nested revenue value
-- statement:
--   The three-branch scalar recursion for next-class revenue from clipped seats and the lower-level value.
-- source:
--   Cause-linked repair of failed extracted definition publication 95be84b8-298c-4747-9878-a2031d06f14b; exact source definition at declaration 024, adding only noncomputable because Real.decidableLT is noncomputable.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

noncomputable def d9NextRevenue (g : ℝ → ℝ) (p x fare s : ℝ) : ℝ :=
  if s < p then g s
  else if s < p + x then (s - p) * fare + g p
  else x * fare + g (s - x)


