-- Prove2me | Definitions.Def_FD1D_Basic
-- name    : FD1D_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:31:49.757338+00:00
-- url     : https://prove2.me/theorems/5c654bbe-1c65-4fb3-96c0-9012e7473e7f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Basic.lean

import Mathlib
set_option autoImplicit true
namespace FD1D
noncomputable section
def policyA (m : ℕ) : ℕ := 200 * ⌈Real.logb 2 (m + 1)⌉₊
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ x, μ.mass x * f x
end FiniteLaw
end
end FD1D


