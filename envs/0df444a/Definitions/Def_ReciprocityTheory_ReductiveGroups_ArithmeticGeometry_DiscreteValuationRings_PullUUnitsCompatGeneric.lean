-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:24.141792+00:00
-- url     : https://prove2.me/theorems/1f2e0c90-30e1-4e38-87dc-5261b22d0072
-- title:
--   Pull UUnits Compat Generic
-- statement:
--   Definitions and structural lemmas for Pull UUnits Compat Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullUUnitsCompatGeneric.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
def scaleGen {M : LB Y} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M where
  s j := res le_top c * t.s j
end ReciprocityTheory.ChartRestriction.G.DVR


