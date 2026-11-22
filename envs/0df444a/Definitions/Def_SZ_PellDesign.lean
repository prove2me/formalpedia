-- Prove2me | Definitions.Def_SZ_PellDesign
-- name    : SZ_PellDesign
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:41:35.168942+00:00
-- url     : https://prove2.me/theorems/2b6611c8-20c8-4262-83ec-07503b010847
-- title:
--   Pell Design
-- statement:
--   Definitions and structural lemmas for Pell Design, from Ralf Stephan's pinned Even floors of powers of the silver ratio development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/PellDesign.lean

import Definitions.Def_SZ_Trace
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false
namespace SZ
structure Pair (α β : ℝ) (a b : ℤ) : Prop where
  /-- the dominant root exceeds `1` -/
  one_lt : 1 < α
  /-- the second root is inside the unit disc -/
  absLt : |β| < 1
  /-- `α + β = a` -/
  sum : α + β = (a : ℝ)
  /-- `α β = -b` -/
  prod : α * β = -(b : ℝ)
namespace Pair
variable {α β : ℝ} {a b : ℤ}
end Pair
noncomputable def xiDesign (α β : ℝ) : ℝ := -β / (α - β)
noncomputable def xiDesign' (α β : ℝ) : ℝ := α / (α - β)
variable {α β : ℝ} {a b : ℤ}
end SZ


