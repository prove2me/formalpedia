-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:36.644298+00:00
-- url     : https://prove2.me/theorems/11d9b724-8532-5c77-913f-6eed31544c76
-- title:
--   Push RProd Pts Res P
-- statement:
--   Definitions and structural lemmas for Push RProd Pts Res P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
section Local
variable (p : Ideal S) [p.IsPrime]
abbrev Gp : Over (Spec (CommRingCat.of (Localization.AtPrime p))) := (Over.pullback (fB S (Localization.AtPrime p))).obj G
def resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p :=
  pullR G (spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v)
variable [∀ s : S, Smooth (Gs G s).hom]
end Local
end ReciprocityTheory.ChartRestriction.G.Chart


