-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EqOfSimilitudeIsoQuotientKernelInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EqOfSimilitudeIsoQuotientKernelInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:23.468277+00:00
-- url     : https://prove2.me/theorems/b8a365ca-88d5-41b9-966f-6927fa8c296b
-- title:
--   Eq Of Similitude Iso Quotient Kernel Invariant
-- statement:
--   Definitions and structural lemmas for Eq Of Similitude Iso Quotient Kernel Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/EqOfSimilitudeIsoQuotientKernelInvariant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EqOfInvariantGenTranslates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
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
noncomputable section
namespace GlobalTheory.KeyKa
section
variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r₀ : Fin 4)
def rowEmb : x.P.A ⟶ Out.powObj x.P.A 4 :=
  (Out.powIsLimit x.P.A 4).lift (Fan.mk x.P.A fun c => (𝟙 x.P.A) ^ al r₀ c)
end
end GlobalTheory.KeyKa
end


