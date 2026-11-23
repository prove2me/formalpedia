-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:01.431966+00:00
-- url     : https://prove2.me/theorems/51e432e5-e2ac-46d2-b8f8-e6877206628c
-- title:
--   Tangent Eq Lc Zero
-- statement:
--   Definitions and structural lemmas for Tangent Eq Lc Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/TangentEqLcZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
def intRing (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {x y} hx hy := by
    show 0 ≤ v (x * y); rw [v.map_mul]; exact add_nonneg hx hy
  one_mem' := by show 0 ≤ v 1; rw [v.map_one]
  add_mem' {x y} hx hy := le_trans (le_min hx hy) (v.map_add x y)
  zero_mem' := by show 0 ≤ v 0; rw [v.map_zero]; exact le_top
  neg_mem' {x} hx := by show 0 ≤ v (-x); rw [v.map_neg]; exact hx
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb


