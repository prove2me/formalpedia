-- Prove2me | Definitions.Def_SZ_DigitParity
-- name    : SZ_DigitParity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:55.651148+00:00
-- url     : https://prove2.me/theorems/39a8ce0f-5a90-444a-a74c-c6a6ffd9540f
-- title:
--   Digit Parity
-- statement:
--   Definitions and structural lemmas for Digit Parity, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace SZ
open Finset Filter Topology
noncomputable def digitSum (m : ℕ) (d : ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (d i : ℝ) / (m : ℝ) ^ (i + 1)
noncomputable def digitReal (m : ℕ) (d : ℕ → ℤ) : ℝ := ⨆ k, digitSum m d k
structure IsDigits (m : ℕ) (d : ℕ → ℤ) : Prop where
  two_le : 2 ≤ m
  nonneg : ∀ i, 0 ≤ d i
  le_sub_one : ∀ i, d i ≤ (m : ℤ) - 1
namespace IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
end IsDigits
variable {m : ℕ} {d : ℕ → ℤ}
end SZ


