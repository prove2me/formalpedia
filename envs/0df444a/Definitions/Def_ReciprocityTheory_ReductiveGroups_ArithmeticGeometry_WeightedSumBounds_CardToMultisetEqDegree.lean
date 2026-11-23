-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:32.514732+00:00
-- url     : https://prove2.me/theorems/531b8e26-2169-4362-9d9d-39de16e4531f
-- title:
--   Card To Multiset Eq Degree
-- statement:
--   Definitions and structural lemmas for Card To Multiset Eq Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
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
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
def expC (q : ℕ) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.subst (PowerSeries.X ^ q : PowerSeries C) (ga a)
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb


