-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:48.012016+00:00
-- url     : https://prove2.me/theorems/7de1246b-4b1a-4b64-8be7-d591e5b088bf
-- title:
--   Mem Nonzero Locus Prod Sec
-- statement:
--   Definitions and structural lemmas for Mem Nonzero Locus Prod Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean

import Mathlib
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
namespace GlobalTheory.BoxSection
theorem res_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (a : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
theorem appLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : U' ≤ U)
    (e : W ≤ f ⁻¹ᵁ U') (e' : W ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U' W e).hom ((X.presheaf.map (homOfLE h).op).hom a) = (f.appLE U W e').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
noncomputable def prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (t : K → L.Sec) : (LB.LinComb L φ (fun _ => 1)).Sec where
  f jj := ∏ i, ((φ i).appLE _ (LB.wchart L φ jj) (LB.wchart_le L φ jj i)).hom ((t i).f (jj i))
  compat jj jj' := by
    have hg : @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') =
        ∏ i, ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom (L.g (jj i) (jj' i) : Γ(X, _)) := by
      simp only [LB.LinComb, zpow_one, Units.coe_prod]
      rfl
    change (Y.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj)).op).hom (∏ i, _) =
      @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') *
      (Y.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj')).op).hom (∏ i, _)
    rw [hg, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e := congrArg ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom ((t i).compat (jj i) (jj' i))
    rw [map_mul] at e
    refine (res_appLE _ _ _ _).trans (((appLE_res _ _ _ _ _).symm.trans e).trans ?_)
    congr 1
    exact (appLE_res _ _ _ _ _).trans (res_appLE _ _ _ _).symm
end GlobalTheory.BoxSection


