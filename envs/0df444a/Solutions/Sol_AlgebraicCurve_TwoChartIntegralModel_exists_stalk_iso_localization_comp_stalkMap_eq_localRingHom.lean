-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d437c711-dc00-53e7-a952-f3f81daa12c1

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₁ : Type u) [Field F₁] [Algebra R F₁] (j₁ : F₁) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin R F₁ j₁) →ₐ[R] ↥(chartAlgFin R F j))
    (m : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F₁ j₁)
    (hmF : Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F₁ j₁ = ιFin R F j ≫ m)
    (y : ↥(XFin R F j)) :
    ∃ (e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅
          CommRingCat.of (Localization.AtPrime y.asIdeal))
      (e₁ : (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk (m.base ((ιFin R F j).base y)) ≅
          CommRingCat.of (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom))),
      (∀ r : R, e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ r : R, e₁.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.germ ⊤ (m.base ((ιFin R F j).base y)) trivial).hom
            (((toBase R F₁ j₁).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom)) r) ∧
      e₁.hom ≫ CommRingCat.ofHom
          (Localization.localRingHom (y.asIdeal.comap ιF.toRingHom) y.asIdeal ιF.toRingHom rfl) =
        m.stalkMap ((ιFin R F j).base y) ≫ e.hom := by

  let y₁ : ↥(XFin R F₁ j₁) := PrimeSpectrum.comap ιF.toRingHom y
  have hpt : (ιFin R F₁ j₁).base y₁ = m.base ((ιFin R F j).base y) := by
    have h := congrArg (fun f => f.base y) hmF
    exact ((Scheme.Hom.comp_apply _ _ y).symm.trans h).trans (Scheme.Hom.comp_apply _ _ y)

  let e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅ CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    asIso ((ιFin R F j).stalkMap y) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y
  have he : e.hom = (ιFin R F j).stalkMap y ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom := rfl
  let c : (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk (m.base ((ιFin R F j).base y)) ≅ (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk ((ιFin R F₁ j₁).base y₁) :=
    (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalkCongr (.of_eq hpt.symm)
  let e₁ : (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk (m.base ((ιFin R F j).base y)) ≅ CommRingCat.of (Localization.AtPrime y₁.asIdeal) :=
    c ≪≫ asIso ((ιFin R F₁ j₁).stalkMap y₁) ≪≫ Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F₁ j₁)) y₁
  have he₁ : e₁.hom = c.hom ≫ (ιFin R F₁ j₁).stalkMap y₁ ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F₁ j₁)) y₁).hom := rfl
  have hc : c.hom = (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalkSpecializes (specializes_of_eq hpt) := rfl

  have key1 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toBase R F j).app ⊤ ≫
      (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial ≫ e.hom =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime y.asIdeal)) := by
    rw [he]
    erw [Scheme.Hom.germ_stalkMap_assoc (ιFin R F j) ⊤ y trivial]
    have h2 : (toBase R F j).app ⊤ ≫ (ιFin R F j).app ⊤ =
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)))).app ⊤ := by
      rw [← ιFin_toBase]; rfl
    erw [reassoc_of% h2]
    erw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    show CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j)) ≫ (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv ≫
      (Spec (CommRingCat.of ↥(chartAlgFin R F j))).presheaf.germ ⊤ y trivial ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F j)) y).hom = _
    rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal)]

  have key2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toBase R F₁ j₁).app ⊤ ≫
      (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.germ ⊤ (m.base ((ιFin R F j).base y)) trivial ≫ e₁.hom =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime y₁.asIdeal)) := by
    rw [he₁, hc]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    erw [Scheme.Hom.germ_stalkMap_assoc (ιFin R F₁ j₁) ⊤ y₁ trivial]
    have h2 : (toBase R F₁ j₁).app ⊤ ≫ (ιFin R F₁ j₁).app ⊤ =
        (Spec.map (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F₁ j₁)))).app ⊤ := by
      rw [← ιFin_toBase]; rfl
    erw [reassoc_of% h2]
    erw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    show CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F₁ j₁)) ≫ (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F₁ j₁))).inv ≫
      (Spec (CommRingCat.of ↥(chartAlgFin R F₁ j₁))).presheaf.germ ⊤ y₁ trivial ≫ (Spec.stalkIso (CommRingCat.of ↥(chartAlgFin R F₁ j₁)) y₁).hom = _
    rw [Spec.germ_stalkMapIso_hom, Iso.inv_hom_id_assoc, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R ↥(chartAlgFin R F₁ j₁) (Localization.AtPrime y₁.asIdeal)]

  have h3 : m.stalkMap ((ιFin R F j).base y) ≫ (ιFin R F j).stalkMap y =
      c.hom ≫ (ιFin R F₁ j₁).stalkMap y₁ ≫ (Spec.map (CommRingCat.ofHom ιF.toRingHom)).stalkMap y := by
    have hA := Scheme.Hom.stalkMap_comp (ιFin R F j) m y
    have hB := Scheme.Hom.stalkMap_congr_hom _ _ hmF.symm y
    have hC := Scheme.Hom.stalkMap_comp (Spec.map (CommRingCat.ofHom ιF.toRingHom)) (ιFin R F₁ j₁) y
    erw [← hA, hB, hC]
    rfl
  have key3 : e₁.hom ≫ CommRingCat.ofHom
      (Localization.localRingHom (y.asIdeal.comap ιF.toRingHom) y.asIdeal ιF.toRingHom rfl) =
      m.stalkMap ((ιFin R F j).base y) ≫ e.hom := by
    rw [he, he₁, reassoc_of% h3]
    erw [← Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom ιF.toRingHom) y]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  refine ⟨e, e₁, fun r => ?_, fun r => ?_, key3⟩
  · have h := congrArg (fun f => f.hom r) key1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h
  · have h := congrArg (fun f => f.hom r) key2
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h

end S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom (solution)
