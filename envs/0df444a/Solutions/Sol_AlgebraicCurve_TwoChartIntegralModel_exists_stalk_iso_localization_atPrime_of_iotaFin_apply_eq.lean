-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0db8ce99-91e9-5e03-9abe-7ad32292145a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

namespace K1StalkLoc

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X" => AlgebraicCurve.TwoChartIntegralModel R F j
set_option quotPrecheck false in
local notation "B" => (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))

theorem read_germ (y : ↥(XFin R F j)) (t : B) :
    (StructureSheaf.stalkIso B y).symm.toRingEquiv.toCommRingCatIso.hom.hom
      (((Spec (CommRingCat.of B)).presheaf.germ ⊤ y trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom t)) =
      algebraMap B (Localization.AtPrime y.asIdeal) t :=
  (StructureSheaf.stalkIso B y).symm.commutes t

theorem germ_app_appIso_inv (y : ↥(XFin R F j)) (t : Γ(Spec (CommRingCat.of B), ⊤)) :
    ((Spec (CommRingCat.of B)).presheaf.germ ((ιFin R F j) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)) y
        (show (ιFin R F j).base y ∈ (ιFin R F j) ''ᵁ ⊤ from ⟨y, trivial, rfl⟩)).hom
      (((ιFin R F j).app ((ιFin R F j) ''ᵁ ⊤)).hom ((((ιFin R F j).appIso ⊤).inv).hom t)) =
    ((Spec (CommRingCat.of B)).presheaf.germ ⊤ y trivial).hom t := by
  have e4 := CategoryTheory.ConcreteCategory.congr_hom ((ιFin R F j).appIso_inv_app ⊤) t
  rw [CategoryTheory.comp_apply] at e4
  change ((Spec (CommRingCat.of B)).presheaf.germ _ y _) (((ιFin R F j).app _) (((ιFin R F j).appIso ⊤).inv t)) =
    ((Spec (CommRingCat.of B)).presheaf.germ ⊤ y trivial) t
  rw [e4]
  exact TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of B)).presheaf _ y _ t

theorem main (z : ↥X) (y : ↥(XFin R F j)) (hy : (ιFin R F j).base y = z) :
    ∃ e : (X).presheaf.stalk z ≅ CommRingCat.of (Localization.AtPrime y.asIdeal),
      (∀ r : R, e.hom.hom
          (((X).presheaf.germ ⊤ z trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ a : B, e.hom.hom
          ((((X).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
              ((((ιFin R F j).appIso ⊤).inv.hom).comp
                (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) a) =
        algebraMap B (Localization.AtPrime y.asIdeal) a) := by
  classical
  subst hy

  let e₂ : (X).presheaf.stalk ((ιFin R F j).base y) ≅ (Spec (CommRingCat.of B)).presheaf.stalk y :=
    asIso ((ιFin R F j).stalkMap y)
  let e₃ : (Spec (CommRingCat.of B)).presheaf.stalk y ≅ CommRingCat.of (Localization.AtPrime y.asIdeal) :=
    (StructureSheaf.stalkIso B y).symm.toRingEquiv.toCommRingCatIso

  have hmove : ∀ (U : (X).Opens) (hU : (ιFin R F j).base y ∈ U) (s : Γ(X, U)),
      e₂.hom.hom (((X).presheaf.germ U ((ιFin R F j).base y) hU).hom s) =
        ((Spec (CommRingCat.of B)).presheaf.germ ((ιFin R F j) ⁻¹ᵁ U) y hU).hom (((ιFin R F j).app U).hom s) := by
    intro U hU s
    exact Scheme.Hom.germ_stalkMap_apply (ιFin R F j) U y hU s
  refine ⟨e₂ ≪≫ e₃, ?_, ?_⟩
  · intro r
    rw [Iso.trans_hom, CommRingCat.hom_comp, RingHom.comp_apply, hmove]

    have c2 := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appTop (ιFin R F j) (toBase R F j)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
    rw [CategoryTheory.comp_apply] at c2
    have c3 := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B))) r
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at c3
    have c1 : ((ιFin R F j).app ⊤).hom (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap R B r) := by
      change ((ιFin R F j).appTop) (((toBase R F j).appTop) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap R B r)
      have c0 : (ιFin R F j ≫ toBase R F j).appTop =
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop := by
        rw [ιFin_toBase]
      rw [← c2, c0]
      exact c3.symm
    have c4 : ((Spec (CommRingCat.of B)).presheaf.germ ((ιFin R F j) ⁻¹ᵁ ⊤) y trivial).hom
          (((ιFin R F j).app ⊤).hom (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
        ((Spec (CommRingCat.of B)).presheaf.germ ⊤ y trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap R B r)) := by
      rw [c1]; rfl
    rw [c4]
    have h5 := read_germ R F j y (algebraMap R B r)
    rw [← IsScalarTower.algebraMap_apply] at h5
    exact h5
  · intro a
    rw [Iso.trans_hom, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hmove,
      germ_app_appIso_inv R F j y]
    exact read_germ R F j y a

end K1StalkLoc

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin R F j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base y = z) :
    ∃ e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal),
      (∀ r : R, e.hom.hom
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ
                ((AlgebraicCurve.TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
              ((((AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv.hom).comp
                (Scheme.ΓSpecIso (CommRingCat.of
                  ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))).inv.hom)) a) =
        algebraMap (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))
          (Localization.AtPrime y.asIdeal) a) :=
  K1StalkLoc.main R F j z y hy

end S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq (solution)
