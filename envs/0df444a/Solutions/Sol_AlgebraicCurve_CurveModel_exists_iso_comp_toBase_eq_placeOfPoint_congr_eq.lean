-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/294a51ef-6aff-5e84-93c8-cd6b01a48a9d

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isOpenImmersion_of_functionField_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq

universe u v w

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.AlgebraicCurve"

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel Place Place.ext Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring"
p2m_open "AlgebraicCurve"

theorem fromSpecStalk_genericPoint_comp_toBase
    {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of K)) :
    C.fromSpecStalk (genericPoint C) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) := by
  have hb : CommRingCat.ofHom (baseToFunctionField c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
        C.presheaf.germ ⊤ (genericPoint C) trivial := by
    ext a
    rfl
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  have h1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op
      = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : (Spec.map (CommRingCat.ofHom (baseToFunctionField c))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom (baseToFunctionField c) ≫
        (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  rw [h2, hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicCurve

theorem solution
    {K : Type u} [Field K]
    {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (φ : F ≃ₐ[K] F') (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase),
      ∀ x : closedPoints M.C,
        M'.placeOfPoint ⟨e.hom.base x.1, by
            show IsClosed ({e.hom.base x.1} : Set M'.C)
            rw [← Set.image_singleton]
            exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isClosedMap _ x.2⟩
          = Place.congrRingEquiv φ.toRingEquiv (fun a => φ.commutes a) (M.placeOfPoint x) := by

  let ψr : M.C.functionField ≃+* M'.C.functionField :=
    M.ffEquiv.symm.trans (φ.toRingEquiv.trans M'.ffEquiv)
  let ψ : M.C.functionField ≅ M'.C.functionField := ψr.toCommRingCatIso
  have hψinv : ∀ z, ψ.inv.hom z = M.ffEquiv (φ.symm (M'.ffEquiv.symm z)) := fun z => rfl

  have hb : CommRingCat.ofHom (baseToFunctionField M'.toBase) ≫ ψ.inv =
      CommRingCat.ofHom (baseToFunctionField M.toBase) := by
    ext a
    change ψ.inv.hom (baseToFunctionField M'.toBase a) = baseToFunctionField M.toBase a
    rw [hψinv, ← M'.ffEquiv_algebraMap a, RingEquiv.symm_apply_apply,
      show φ.symm (algebraMap K F' a) = algebraMap K F a from φ.symm.commutes a,
      M.ffEquiv_algebraMap]
  have hψ : Spec.map ψ.inv ≫ M'.C.fromSpecStalk (genericPoint M'.C) ≫ M'.toBase =
      M.C.fromSpecStalk (genericPoint M.C) ≫ M.toBase := by
    rw [fromSpecStalk_genericPoint_comp_toBase, fromSpecStalk_genericPoint_comp_toBase,
      ← Spec.map_comp, hb]

  obtain ⟨U, hη, j, himm, hj, hjη⟩ :=
    AlgebraicGeometry.Scheme.exists_isOpenImmersion_of_functionField_iso M.toBase M'.toBase ψ hψ

  haveI : Smooth M'.toBase := SmoothOfRelativeDimension.smooth (n := 1) (f := M'.toBase)
  obtain ⟨e, he, heU⟩ :=
    AlgebraicGeometry.Scheme.exists_iso_comp_eq_of_isOpenImmersion_of_isProper M.toBase M'.toBase
      U ⟨genericPoint M.C, hη⟩ j hj
  refine ⟨e, he, fun x => ?_⟩
  obtain ⟨x, hx⟩ := x
  generalize_proofs hx'

  have hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ e.hom =
      Spec.map ψ.inv ≫ M'.C.fromSpecStalk (genericPoint M'.C) := by
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι U (genericPoint M.C) hη, Category.assoc, heU, hjη]

  have hηx : genericPoint M.C ⤳ x := (genericPoint_spec M.C).specializes trivial
  have hηx' : genericPoint M'.C ⤳ e.hom.base x := (genericPoint_spec M'.C).specializes trivial
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := M.C) hηx
  have h2 := Scheme.SpecMap_stalkMap_fromSpecStalk (f := e.hom) (x := x)
  have h3 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := M'.C) hηx'
  have hstalk : e.hom.stalkMap x ≫ M.C.presheaf.stalkSpecializes hηx =
      M'.C.presheaf.stalkSpecializes hηx' ≫ ψ.inv := by
    apply Spec.map_injective
    rw [← cancel_mono (M'.C.fromSpecStalk (e.hom.base x))]
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, h2, h3,
      ← Category.assoc, h1, hgen]
  have halg : ∀ a', algebraMap (M.C.presheaf.stalk x) M.C.functionField ((e.hom.stalkMap x).hom a')
      = ψ.inv.hom (algebraMap (M'.C.presheaf.stalk (e.hom.base x)) M'.C.functionField a') := by
    intro a'
    have := congrArg (fun g => g.hom a') hstalk
    simpa [RingHom.algebraMap_toAlgebra] using this

  have hsurj : Function.Surjective (e.hom.stalkMap x).hom := by
    haveI : IsIso (e.hom.stalkMap x) := ((isIso_iff_isIso_stalkMap e.hom).mp inferInstance).2 x
    exact (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv.surjective

  have hr := M.range_stalk_eq ⟨x, hx⟩
  have hr' := M'.range_stalk_eq ⟨e.hom.base x, hx'⟩
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  rw [Place.congrRingEquiv_toValuationSubring, ← hr']
  ext z
  simp only [RingHom.mem_range, RingHom.coe_comp, Function.comp_apply]
  change (∃ a', M'.ffEquiv.symm _ = z) ↔ z ∈ (M.placeOfPoint ⟨x, hx⟩).toValuationSubring.comap _
  rw [ValuationSubring.mem_comap]
  change _ ↔ φ.toRingEquiv.symm z ∈ (M.placeOfPoint ⟨x, hx⟩).toValuationSubring
  have hmem : φ.toRingEquiv.symm z ∈ (M.placeOfPoint ⟨x, hx⟩).toValuationSubring ↔
      φ.toRingEquiv.symm z ∈ (M.placeOfPoint ⟨x, hx⟩).toValuationSubring.toSubring := Iff.rfl
  rw [hmem, ← hr, RingHom.mem_range]
  simp only [RingHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨a', rfl⟩
    refine ⟨(e.hom.stalkMap x).hom a', ?_⟩
    change M.ffEquiv.symm (algebraMap _ _ ((e.hom.stalkMap x).hom a')) = _
    rw [halg, hψinv]
    simp only [RingEquiv.symm_apply_apply]
    rfl
  · rintro ⟨a, ha⟩
    obtain ⟨a', rfl⟩ := hsurj a
    refine ⟨a', ?_⟩
    change M.ffEquiv.symm (algebraMap _ _ ((e.hom.stalkMap x).hom a')) = _ at ha
    rw [halg, hψinv] at ha
    simp only [RingEquiv.symm_apply_apply] at ha
    change M'.ffEquiv.symm _ = z
    have ha' : φ.symm (M'.ffEquiv.symm
        (algebraMap (M'.C.presheaf.stalk (e.hom.base x)) M'.C.functionField a')) = φ.symm z := ha
    exact φ.symm.injective ha'

end S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq (solution)
