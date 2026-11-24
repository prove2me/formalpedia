-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:03.026028+00:00
-- url     : https://prove2.me/theorems/a72f60b5-f265-4c44-88aa-d021e25ba962
-- title:
--   Is Square Det Comparison Scale Sec
-- statement:
--   Definitions and structural lemmas for Is Square Det Comparison Scale Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsSquareDetComparisonScaleSec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero
noncomputable section
namespace GlobalTheory.KaScale
section Lin
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))}
def der (v : sp (R₀ := K) (DualNumber K) ⟶ A) (U : A.left.Opens) (f : Γ(A.left, U)) : K :=
  TrivSqZeroExt.snd (valT (T := DualNumber K) v.left U f)
variable [GrpObj A]
end Lin
def cS {K : Type} [CommRing K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (y : Y) : K →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}
end GlobalTheory.KaScale


