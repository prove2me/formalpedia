-- Prove2me | Definitions.Def_SZ_Classification
-- name    : SZ_Classification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:44:00.79292+00:00
-- url     : https://prove2.me/theorems/739b26d8-6b1b-4a6e-9c91-381ddea1d803
-- title:
--   Classification
-- statement:
--   Definitions and structural lemmas for Classification, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/Classification.lean

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
namespace SZ
open Real
def IsQuadPisot (α : ℝ) : Prop :=
  1 < α ∧ ∃ (β : ℝ) (a b : ℤ), β ≠ 0 ∧ |β| < 1 ∧ α + β = (a : ℝ) ∧ α * β = -(b : ℝ)
end SZ


