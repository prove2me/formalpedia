-- Prove2me | Definitions.Def_d9LeftSlope
-- name    : d9LeftSlope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T10:33:14.188952+00:00
-- url     : https://prove2.me/theorems/68ea2a32-13b3-44b2-a048-8e3b9dc09ffb
-- title:
--   Left-sided sample revenue slope
-- statement:
--   The recursive sample slope for the left derivative of nested revenue, with closed branch endpoints.
-- source:
--   Cause-linked repair of failed source-extracted definition publication 099fcd12-0030-4d9f-8702-99a2aecc3e4c; adds only noncomputable required by Real.decidableLE.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

/-- The left-hand seat slope uses closed branch endpoints: at protection the
left branch is inherited, and at capacity the affine branch is inherited. -/
noncomputable def d9LeftSlope (f p x : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if s ≤ x 1 then f 1 else 0
  | n + 2, s =>
      if s ≤ p (n + 1) then d9LeftSlope f p x (n + 1) s
      else if s ≤ p (n + 1) + x (n + 2) then f (n + 2)
      else d9LeftSlope f p x (n + 1) (s - x (n + 2))


