-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_FinExtHomInjective
-- name    : Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_FinExtHomInjective
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:10.161486+00:00
-- url     : https://prove2.me/theorems/16e80ce3-d362-44f8-86e9-5010e709f155
-- title:
--   Fin Ext Hom Injective
-- statement:
--   Definitions and structural lemmas for Fin Ext Hom Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/FinExtHomInjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests
section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
end Ext
section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
end Tors
end GlobalTheory.UU.RelTests
end


