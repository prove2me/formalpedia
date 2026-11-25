-- Prove2me | Definitions.Def_SZ_CoverGame
-- name    : SZ_CoverGame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:38:55.129695+00:00
-- url     : https://prove2.me/theorems/495a0046-6db9-453e-ae42-939d816c82b0
-- title:
--   Cover Game
-- statement:
--   Definitions and structural lemmas for Cover Game, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace SZ
open Filter Topology
noncomputable def pick (w : ℝ) : ℤ × ℤ :=
  if w ≤ 1 + Real.sqrt 3 then (0, 0)
  else if w < 2 * Real.sqrt 3 then (2, 0)
  else if w ≤ 1 + 3 * Real.sqrt 3 then (0, 2)
  else (2, 2)
noncomputable def coverState : ℕ → ℤ × ℤ
  | 0 => (-12, 9)
  | k + 1 =>
      (3 * ((coverState k).1 - (pick (((coverState k).1 : ℝ)
              + ((coverState k).2 : ℝ) * Real.sqrt 3)).1),
       3 * ((coverState k).2 - (pick (((coverState k).1 : ℝ)
              + ((coverState k).2 : ℝ) * Real.sqrt 3)).2))
noncomputable def W (k : ℕ) : ℝ :=
  ((coverState k).1 : ℝ) + ((coverState k).2 : ℝ) * Real.sqrt 3
noncomputable def digitA (k : ℕ) : ℤ := (pick (W k)).1
noncomputable def digitB (k : ℕ) : ℤ := (pick (W k)).2
end SZ


