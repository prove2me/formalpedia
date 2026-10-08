-- Prove2me | Definitions.Def_d9ResidualSeatStep
-- name    : d9ResidualSeatStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T10:44:41.048333+00:00
-- url     : https://prove2.me/theorems/b434627e-0cca-4878-b467-060a88525496
-- title:
--   Residual seat count after one protection step
-- statement:
--   The recursive residual-seat value selected by the protection and demand thresholds.
-- source:
--   Cause-linked repair of failed extracted definition publication 0641fe30-adfd-4867-bc87-920cbcdbdc91; exact source definition at declaration 002, adding only noncomputable because Real.decidableLT is noncomputable.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

/-- The seat count passed to the lower recursion branch at one protection step. -/
noncomputable def d9ResidualSeatStep (p x : ℕ → ℝ) (i : ℕ) (s : ℝ) : ℝ :=
  if s < p i then s
  else if s < p i + x (i + 1) then p i
  else s - x (i + 1)


