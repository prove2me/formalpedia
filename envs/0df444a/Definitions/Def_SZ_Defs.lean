-- Prove2me | Definitions.Def_SZ_Defs
-- name    : SZ_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:40:07.312886+00:00
-- url     : https://prove2.me/theorems/87e13e24-2572-4237-bfa1-7510471d7030
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Defs.lean

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
set_option autoImplicit false
namespace SZ
open Int
def MahlerZ : Set ℝ :=
  {α : ℝ | 1 < α ∧ ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * α ^ n⌋}
def S : Set ℝ := {α : ℝ | 1 < α} \ MahlerZ
def MahlerQuestion : Prop := ((3 : ℝ) / 2) ∈ MahlerZ
def Problem5 : Prop := ∃ α ∈ S, 2 < α
end SZ


