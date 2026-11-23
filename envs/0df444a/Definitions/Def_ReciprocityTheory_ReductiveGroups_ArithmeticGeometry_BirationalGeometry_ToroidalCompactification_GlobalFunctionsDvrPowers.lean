-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrPowers
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:38.278851+00:00
-- url     : https://prove2.me/theorems/896a7807-a909-40a0-99c3-4a1ffb973902
-- title:
--   Global Functions Dvr Powers
-- statement:
--   Definitions and structural lemmas for Global Functions Dvr Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrPowers.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
def pullPowIso {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) :
    ∀ n : ℕ, (Over.pullback f).obj (powObj G n) ≅ powObj ((Over.pullback f).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback f)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback f) G (powObj G n)).symm ≪≫
      whiskerLeftIso ((Over.pullback f).obj G) (pullPowIso f G n)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers


