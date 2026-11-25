-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:46:03.167084+00:00
-- url     : https://prove2.me/theorems/1b1b4f95-1e29-5891-bb07-b54f3d44b215
-- title:
--   Exists Away Not Mem
-- statement:
--   Definitions and structural lemmas for Exists Away Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ExistsAwayNotMem.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]
section Prime
variable (p : Ideal S) [p.IsPrime]
@[instance_reducible]
def awayAtPrime (t : S) (ht : t ∉ p) : Algebra (Localization.Away t) (Localization.AtPrime p) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) p.primeCompl
    ((Submonoid.powers_le (P := p.primeCompl)).mpr ht)
end Prime
end ReciprocityTheory.ChartRestriction.G.Chart


