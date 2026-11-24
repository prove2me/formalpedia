-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOneOfPowOfClosedPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.004396+00:00
-- url     : https://prove2.me/theorems/e08022e4-57f7-4926-a4c9-4f26dc4cf07f
-- title:
--   Eq One Of Pow Of Closed Point
-- statement:
--   Definitions and structural lemmas for Eq One Of Pow Of Closed Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/EqOneOfPowOfClosedPoint.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.RedPts
variable {S : Scheme.{0}}
def precomp (G : Over S) [GrpObj G] {T T' : Over S} (u : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := u ≫ x
  map_one' := MonObj.comp_one u
  map_mul' x y := MonObj.comp_mul u x y
def diagSec {T : Scheme.{0}} (p : T ⟶ S) : 𝟙_ (Over T) ⟶ (Over.pullback p).obj (Over.mk p) :=
  Over.homMk (pullback.lift (𝟙 T) (𝟙 T) rfl) (pullback.lift_snd _ _ _)
def toSec (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    (Over.mk p ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback p).obj G) :=
  (precomp _ (diagSec p)).comp (Over.pullback p).homMonoidHom
end GlobalTheory.RedPts


