-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/78a2a3d5-2054-5afa-817b-784980cc98cd

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XInf R F j))
    (hz : (ιInf R F j).base y ∈ (ιInf R F j) ''ᵁ ⊤) :
    ∃ e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y) ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal),
      (∀ r : R, e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιInf R F j).base y) trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ a : ↥(chartAlgInf R F j), e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) hz).hom
            ((((ιInf R F j).appIso ⊤).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom a)))) =
        algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal) a) := by
  let e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y) ≅
      CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    asIso ((ιInf R F j).stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y
  have he : e.hom = (ιInf R F j).stalkMap y ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).hom := rfl

  have key1 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toBase R F j).app ⊤ ≫
      (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιInf R F j).base y) trivial ≫ e.hom =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime y.asIdeal)) := by
    rw [he]
    erw [Scheme.Hom.germ_stalkMap_assoc (ιInf R F j) ⊤ y trivial]
    have h2 : (toBase R F j).app ⊤ ≫ (ιInf R F j).app ⊤ =
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j)))).app ⊤ := by
      rw [← ιInf_toBase]; rfl
    erw [reassoc_of% h2]
    erw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    show CommRingCat.ofHom (algebraMap R ↥(chartAlgInf R F j)) ≫ (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv ≫
      (Spec (CommRingCat.of ↥(chartAlgInf R F j))).presheaf.germ ⊤ y trivial ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).hom = _
    rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal)]

  have key2 : (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv ≫ ((ιInf R F j).appIso ⊤).inv ≫
      (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) hz ≫ e.hom =
      CommRingCat.ofHom (algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal)) := by
    rw [he, Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appIso_inv_app_assoc, TopCat.Presheaf.germ_res_assoc]
    show (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv ≫
      (Spec (CommRingCat.of ↥(chartAlgInf R F j))).presheaf.germ ⊤ y trivial ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgInf R F j)) y).hom = _
    rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc]
  refine ⟨e, fun r => ?_, fun a => ?_⟩
  · have h := congrArg (fun f => f.hom r) key1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  · have h := congrArg (fun f => f.hom a) key2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h

end S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf (solution)
