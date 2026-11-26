-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
-- name    : SharpIntermediateSubgroupBounds_GroupMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:44:05.64472+00:00
-- url     : https://prove2.me/theorems/6d2f0c2e-060d-471b-a265-8572eb315b46
-- title:
--   Group Main
-- statement:
--   Definitions and structural lemmas for Group Main, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/GroupMain.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
def indexLog (q n : ℕ) : ℝ :=
  Real.log (n : ℝ) / Real.log (q : ℝ)
def sharpScale (q n : ℕ) : ℝ :=
  Real.exp (Real.log (q : ℝ) * indexLog q n ^ 2 / 4)
end
end SharpIntermediateSubgroupBounds


