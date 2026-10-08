-- Prove2me | Definitions.Def_d9RightSlope
-- name    : d9RightSlope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T10:32:47.834982+00:00
-- url     : https://prove2.me/theorems/60dbf7e8-28b1-439b-8fa9-ef607d9d78f3
-- title:
--   Right-sided sample revenue slope
-- statement:
--   The recursive sample slope for the right derivative of nested revenue, with strict branch thresholds.
-- source:
--   Cause-linked repair of failed source-extracted definition publication baea04fc-5653-4a11-849a-f55e891066f6; adds only noncomputable required by Real.decidableLT.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

noncomputable def d9RightSlope (f p x : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if s < x 1 then f 1 else 0
  | n + 2, s =>
      if s < p (n + 1) then d9RightSlope f p x (n + 1) s
      else if s < p (n + 1) + x (n + 2) then f (n + 2)
      else d9RightSlope f p x (n + 1) (s - x (n + 2))


