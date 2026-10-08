-- Prove2me | Definitions.Def_d9ProtectionRightSlope
-- name    : d9ProtectionRightSlope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T12:39:07.435002+00:00
-- url     : https://prove2.me/theorems/997770e2-64f9-4195-81a7-ecaad622572c
-- title:
--   d9ProtectionRightSlope
-- statement:
--   The right derivative of nested revenue with respect to protection coordinate j, recursively transported through later seat-allocation branches. Classical real comparisons make this definition noncomputable.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9RightSlope
open NestedSeatAlloc.IntPolicy

/-- One-sided right slope of revenue as a function of a single protection coordinate. Later levels transport it through the active recursion branches. -/
noncomputable def d9ProtectionRightSlope (f p x : ℕ → ℝ) (j : ℕ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, s =>
      if n + 1 < j then 0
      else if n + 1 = j then
        if p j < s ∧ s ≤ p j + x (j + 1) then d9RightSlope f p x j (p j) - f (j + 1) else 0
      else if s < p (n + 1) then d9ProtectionRightSlope f p x j (n + 1) s
      else if s < p (n + 1) + x (n + 2) then d9ProtectionRightSlope f p x j (n + 1) (p (n + 1))
      else d9ProtectionRightSlope f p x j (n + 1) (s - x (n + 2))


