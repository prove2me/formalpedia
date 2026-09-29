-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.eq_zero_of_comp_translation_eq_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7cb33c04-c8c8-5e7c-9ffc-10877555e61c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

namespace FreeTranslation
set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

theorem comp_toPoint_eq_of_comp_translation_eq {V : Scheme.{0}} (h : V ⟶ A) (R : L.AlgPoints hc k)
    (hfix : h ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint R) = h) :
    (h ≫ f) ≫ (RelativeGroupLaw.AlgPoints.toPoint R).1 =
      (h ≫ f) ≫ (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)).1 := by
  set t : V ⟶ Spec (CommRingCat.of k) := h ≫ f with ht

  let hV : SchemeHomOver t f := ⟨h, rfl⟩
  let RV : SchemeHomOver t f := schemeHomOverComp h rfl (constPt f (RelativeGroupLaw.AlgPoints.toPoint R))
  have hmul : L.mul t hV RV = hV := by
    have hnat := L.mul_natural f t h rfl RelativeGroupLaw.idPoint (constPt f (RelativeGroupLaw.AlgPoints.toPoint R))
    have e1 : schemeHomOverComp h rfl (RelativeGroupLaw.idPoint (f := f)) = hV := Subtype.ext (Category.comp_id h)
    rw [e1] at hnat
    rw [← hnat]
    exact Subtype.ext hfix
  have hone : RV = L.one t := by
    calc RV = L.mul t (L.one t) RV := (L.one_mul t RV).symm
      _ = L.mul t (L.mul t (L.inv t hV) hV) RV := by rw [L.inv_mul_cancel]
      _ = L.mul t (L.inv t hV) (L.mul t hV RV) := by rw [L.mul_assoc]
      _ = L.mul t (L.inv t hV) hV := by rw [hmul]
      _ = L.one t := L.inv_mul_cancel t hV
  have hone' : L.one t =
      schemeHomOverComp (h ≫ f) (by rw [specMap_algebraMap_self, Category.comp_id])
        (L.one (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
    (L.one_natural _ _ _ _).symm
  have hv := congrArg Subtype.val (hone.trans hone')
  simp only [RV, GoodReductionJacobian.schemeHomOverComp_coe, constPt, RelativeGroupLaw.AlgPoints.toPoint_zero, Category.assoc] at hv
  exact hv

theorem eq_zero_of_comp_translation_eq {V : Scheme.{0}} [Nonempty V] (h : V ⟶ A) (R : L.AlgPoints hc k)
    (hfix : h ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint R) = h) : R = 0 := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have key := comp_toPoint_eq_of_comp_translation_eq f L hc h R hfix
  have key' := congrArg (fun g => V.fromSpecResidueField v ≫ g) key
  simp only [← Category.assoc] at key'
  have key'' : Spec.map (Spec.preimage ((V.fromSpecResidueField v ≫ h) ≫ f)) ≫ (RelativeGroupLaw.AlgPoints.toPoint R).1 =
      Spec.map (Spec.preimage ((V.fromSpecResidueField v ≫ h) ≫ f)) ≫
        (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)).1 := by
    rw [Spec.map_preimage]
    exact key'
  have := AlgebraicGeometry.eq_of_specMap_comp_eq_of_field
    (Spec.preimage ((V.fromSpecResidueField v ≫ h) ≫ f)).hom
    (RelativeGroupLaw.AlgPoints.toPoint R).1 (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)).1
    (by simpa only [CommRingCat.ofHom_hom] using key'')
  exact RelativeGroupLaw.AlgPoints.ext (Subtype.ext this)

theorem eq_zero_of_comp_translation_eq' {Z : Scheme.{0}} (hZ : Nonempty Z) (v : Z ⟶ A) (P : L.AlgPoints hc k)
    (h : v ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P) = v) : P = 0 := by
  haveI := hZ
  exact eq_zero_of_comp_translation_eq f L hc v P h

end FreeTranslation

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {Z : Scheme.{0}} (hZ : Nonempty ↥Z) (v : Z ⟶ A) (P : L.AlgPoints hc k)
    (h : v ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P) = v) :
    P = 0 :=
  FreeTranslation.eq_zero_of_comp_translation_eq' f L hc hZ v P h

end S_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty (solution)
