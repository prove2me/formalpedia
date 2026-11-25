-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:06.858543+00:00
-- url     : https://prove2.me/theorems/df8dd7be-b288-4ef0-98cb-48e37c06c4aa
-- title:
--   Pair Compat
-- statement:
--   Definitions and structural lemmas for Pair Compat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PairCompat.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
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
abbrev Rv {S : Type} [CommRing S] (a b c : S) : Type := Localization.Away (algebraMap S (Qv a b) c)
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]
end ReciprocityTheory.ChartRestriction.G.Chart


