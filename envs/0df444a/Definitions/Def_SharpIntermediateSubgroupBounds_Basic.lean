-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Basic
-- name    : SharpIntermediateSubgroupBounds_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:19.956432+00:00
-- url     : https://prove2.me/theorems/06a82768-85f7-5c0c-a082-d3909c2ddbe1
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Basic.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
def gammaNum (p r : ℕ) : ℕ :=
  ∏ j ∈ Finset.range r, (p ^ (j + 1) - 1)
def gammaDen (p r : ℕ) : ℕ :=
  p ^ (r * (r + 1) / 2)
def gammaQ (p r : ℕ) : ℚ :=
  (gammaNum p r : ℚ) / gammaDen p r
end SharpIntermediateSubgroupBounds


