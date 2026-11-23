-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PwIsoIsGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:35.507703+00:00
-- url     : https://prove2.me/theorems/0693cd99-1acc-4815-b895-e9f3b149e277
-- title:
--   Pw Iso Is Gen
-- statement:
--   Definitions and structural lemmas for Pw Iso Is Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PwIsoIsGen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
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
namespace GlobalTheory.KeyVia
variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}
def Via (w : LB.Iso L' (L.pull φ)) (l : ℕ) (a' : ∀ i, Γ(Y, L'.U i)) (a : ∀ j, Γ(X, L.U j)) : Prop :=
  ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (a (j PUnit.unit)) =
      (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (a' i)
theorem chart_le (j : (L.pull φ).ι) : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
  LB.wchart_le L (fun _ => φ) j PUnit.unit
def pwIso {A B : LB Y} (w : LB.Iso A B) (t : ℤ) : LB.Iso (pw A t) (pw B t) := ⟨fun p => w.s p ^ t⟩
theorem res_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e
theorem appLE_res {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e
theorem pull_g (j j' : (L.pull φ).ι) (h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    (L.pull φ).g j j' = Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit)) := by
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique]
  exact (zpow_one (Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit))))
def pullSec (φ : Y ⟶ X) {t : ℤ} (s : LB.Sec (pw L t)) : LB.Sec (pw (L.pull φ) t) where
  f j := (φ.appLE _ _ (chart_le j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hy => ⟨chart_le j hy.1, chart_le j' hy.2⟩
    have e := (congrArg (φ.appLE _ _ h).hom (s.compat (j PUnit.unit) (j' PUnit.unit))).trans (map_mul _ _ _)
    refine (res_appLE _ _ _).trans ((appLE_res h _ _).symm.trans (e.trans (congrArg₂ (· * ·) ?_
      ((appLE_res h _ _).trans (res_appLE _ _ _).symm))))
    exact (congrArg Units.val ((congrArg (· ^ t) (pull_g j j' h)).trans (map_zpow _ _ t).symm)).symm
end GlobalTheory.KeyVia
end


