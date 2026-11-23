-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:41.762368+00:00
-- url     : https://prove2.me/theorems/155114ef-3b14-458d-af78-f7bc052d2250
-- title:
--   Exists Line Bundle Height Proper Scheme
-- statement:
--   Definitions and structural lemmas for Exists Line Bundle Height Proper Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperScheme.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
namespace GlobalTheory.SS.Height
open IsLocalRing
def ev (R : Type) [CommRing R] [IsLocalRing R] : (Sp R).presheaf.stalk (closedPoint R) →+* R :=
  (stalkClosedPointIso (CommRingCat.of R)).hom.hom
variable {k K : Type} [Field k] [Field K] [Algebra k K]
def ord (Pl : Places k K) (i : Pl.I) : ((Sp K).presheaf.stalk (closedPoint K))ˣ →* Multiplicative ℤ :=
  (MonoidHom.mk' (fun x : Kˣ => Multiplicative.ofAdd (Pl.v i x)) fun x y => by
    rw [Pl.v_mul, ofAdd_add]).comp (Units.map (ev K).toMonoidHom)
def od (Pl : Places k K) (i : Pl.I) (u : ((Sp K).presheaf.stalk (closedPoint K))ˣ) : ℤ := (ord Pl i u).toAdd
variable (Pl : Places k K)
end GlobalTheory.SS.Height
namespace GlobalTheory.SS
open IsLocalRing Height
end GlobalTheory.SS


