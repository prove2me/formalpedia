-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNormalisingUnitSimilitudeOrigin
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:54.567865+00:00
-- url     : https://prove2.me/theorems/4ac5f931-b172-5284-89c7-2b2b02d047cc
-- title:
--   Exists Normalising Unit Similitude Origin
-- statement:
--   Definitions and structural lemmas for Exists Normalising Unit Similitude Origin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNormalisingUnitSimilitudeOrigin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

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
namespace GlobalTheory.SimilUnit
section Rep
variable {X Y Y' : Scheme.{0}} (L : LB X)
def IsVal (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ y J, Good L y J → val t (𝟙 Y) y J = v y J
variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}
theorem IsVal.one : IsVal L (Y := Y) (fun _ _ _ => 1) (fun _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, fun i j => by
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _), fun _ _ _ => Fintype.prod_empty _, fun _ _ _ => val_one _⟩
theorem IsVal.mul (a : IsVal L F v) (b : IsVal L F' v') :
    IsVal L (fun U _ h => F U h * F' U h) (fun y J => v y J * v' y J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv y J hJ, hv' y J hJ]
theorem IsVal.prod {I : Type} {G : I → ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    {u : I → ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ} (a : ∀ i, IsVal L (G i) (u i)) (s : Finset I) :
    IsVal L (fun U _ h => ∏ i ∈ s, G i U h) (fun y J => ∏ i ∈ s, u i y J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using IsVal.one
  | insert d s hd ih => simpa only [Finset.prod_insert hd] using (a d).mul ih
end Rep
end GlobalTheory.SimilUnit


