-- Prove2me | Definitions.Def_SZ_Tijdeman
-- name    : SZ_Tijdeman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:41:03.604028+00:00
-- url     : https://prove2.me/theorems/9e076cd9-74c6-4f74-b5c0-f8e0e2906b24
-- title:
--   Tijdeman
-- statement:
--   Definitions and structural lemmas for Tijdeman, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Tijdeman.lean

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
set_option autoImplicit false
namespace SZ
variable {α : ℝ}
noncomputable def greedy (α : ℝ) : ℕ → ℤ
  | 0 => 2
  | (n + 1) => 2 * ⌈α * (greedy α n : ℝ) / 2⌉
noncomputable def gLo (α : ℝ) (n : ℕ) : ℝ := (greedy α n : ℝ) / α ^ n
noncomputable def gHi (α : ℝ) (n : ℕ) : ℝ := ((greedy α n : ℝ) + 1) / α ^ n
noncomputable def tijdemanWitness (α : ℝ) : ℝ := ⨆ n : ℕ, gLo α n
end SZ


