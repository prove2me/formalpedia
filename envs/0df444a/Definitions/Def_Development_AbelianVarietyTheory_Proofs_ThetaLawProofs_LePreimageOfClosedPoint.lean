-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LePreimageOfClosedPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:11.322798+00:00
-- url     : https://prove2.me/theorems/5507695f-f641-4d57-816a-a02203b276e3
-- title:
--   Le Preimage Of Closed Point
-- statement:
--   Definitions and structural lemmas for Le Preimage Of Closed Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/LePreimageOfClosedPoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
namespace GlobalTheory.FormalChart
section Alg
variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}
end Alg
section Geo
open GlobalTheory.KeyKa.EtBaseChange
variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {T : Type} [CommRing T]
theorem le_preimage (φ : Γ(X, V) →+* T) : ⊤ ≤ (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) ⁻¹ᵁ V :=
  fun _ _ => hV.range_fromSpec.subset (Set.mem_range_self _)
end Geo
end GlobalTheory.FormalChart


