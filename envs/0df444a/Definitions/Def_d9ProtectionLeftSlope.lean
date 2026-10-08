-- Prove2me | Definitions.Def_d9ProtectionLeftSlope
-- name    : d9ProtectionLeftSlope
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T12:38:25.454121+00:00
-- url     : https://prove2.me/theorems/9804f49d-f56e-4fba-a9ed-731bf47ba7cc
-- title:
--   d9ProtectionLeftSlope
-- statement:
--   The left derivative of nested revenue with respect to protection coordinate j, recursively transported through later seat-allocation branches. Classical real comparisons make this definition noncomputable.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:496f4004c17c3685f2a6ca1fe50e48c052a3bd7e6bf49a160e286175e5aa3065

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9LeftSlope
open NestedSeatAlloc.IntPolicy

/-- Left-sided protection-coordinate slope, with interval endpoints matching the left derivative of the cutoff recursion. -/
noncomputable def d9ProtectionLeftSlope (f p x : ℕ → ℝ) (j : ℕ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, s =>
      if n + 1 < j then 0
      else if n + 1 = j then
        if p j ≤ s ∧ s < p j + x (j + 1) then d9LeftSlope f p x j (p j) - f (j + 1) else 0
      else if s < p (n + 1) then d9ProtectionLeftSlope f p x j (n + 1) s
      else if s < p (n + 1) + x (n + 2) then d9ProtectionLeftSlope f p x j (n + 1) (p (n + 1))
      else d9ProtectionLeftSlope f p x j (n + 1) (s - x (n + 2))


