-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ad8802c3-e87d-5c36-98e8-4d884852ecff

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq.AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq.AlgebraicCurve"

universe u v

section E3

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.germ_stalkClosedPointTo_Spec Scheme.Hom.stalkSpecializes_stalkMap Scheme.Hom Scheme.Hom.germ_stalkMap_apply Scheme.stalkClosedPointTo_comp Scheme.SpecMap_stalkSpecializes_fromSpecStalk Spec IsIntegral Spec.map Scheme Scheme.stalkClosedPointTo IsOpenImmersion Scheme.Hom.appIso_inv_app_apply genericPoint_eq_of_isOpenImmersion pointEquivClosedPoint Scheme.SpecMap_stalkMap_fromSpecStalk SpecToEquivOfLocalRing_eq_iff Scheme.Hom.germ_stalkMap SpecToEquivOfLocalRing Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

private theorem e3_genericPoint_specializes :
    θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

private noncomputable def e3_ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (e3_genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
private theorem e3_SpecMap_ffMap_fromSpecStalk :
    Spec.map (e3_ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [e3_ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

private theorem e3_germ_ffMap (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ e3_ffMap θ =
      θ.app U ≫ X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) := by
  rw [e3_ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem e3_ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    e3_ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, e3_germ_ffMap]; rfl

private theorem e3_ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    e3_ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [e3_ffMap_germ_apply]
  rfl

end FFMap

section ChartValue

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

private theorem e3_stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶ Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ trivial w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show Scheme.stalkClosedPointTo l (ι.stalkMap (l.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base (l.base (IsLocalRing.closedPoint R))) h ((ι.appIso ⊤).inv w))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

private theorem e3_stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

end ChartValue

end AlgebraicGeometry

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.pointEquivPlace_apply Place Place.ext SemilinearAut SemilinearAut.toRingAut SemilinearAut.inv_smul_def SemilinearAut.smul_toValuationSubring"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace pointEquivPlace_apply placeOfPoint toBase C range_stalk_eq ffEquiv"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L) (θ : M.C ⟶ M.C) [IsIso θ]

private theorem _root_.AlgebraicCurve.CurveModel.s3_ffMap_algebraMap_stalk (x₁ : M.C) (s : M.C.presheaf.stalk (θ.base x₁)) :
    e3_ffMap θ (algebraMap _ M.C.functionField s) = algebraMap _ M.C.functionField (θ.stalkMap x₁ s) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, e3_ffMap]
  show (M.C.presheaf.stalkSpecializes _ ≫ M.C.presheaf.stalkSpecializes _ ≫ θ.stalkMap _) s =
    (θ.stalkMap x₁ ≫ M.C.presheaf.stalkSpecializes _) s
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  erw [Scheme.Hom.stalkSpecializes_stalkMap θ (genericPoint M.C) x₁ (genericPoint_specializes x₁)]

p2m_export "AlgebraicCurve.CurveModel" "s3_ffMap_algebraMap_stalk"
private theorem s3_isLocalHom_of_field {F : Type*} [Field F] {S : Type*} [CommRing S] [Nontrivial S] (f : F →+* S) :
    IsLocalHom f :=
  ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h0 => by simp [h0] at ha⟩

private theorem _root_.AlgebraicCurve.CurveModel.s3_ffMap_eq_of_fromSpecStalk_comp_eq (φ : L ≃+* L)
    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C)) (w : M.C.functionField) :
    e3_ffMap θ w = M.ffEquiv (φ.symm (M.ffEquiv.symm w)) := by
  have h1 : Spec.map (e3_ffMap θ) ≫ M.C.fromSpecStalk _ =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C) := by
    rw [e3_SpecMap_ffMap_fromSpecStalk, hθgen]
  haveI i1 : IsLocalHom (e3_ffMap θ).hom := s3_isLocalHom_of_field _
  haveI i2 : IsLocalHom (CommRingCat.ofHom
      (M.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M.ffEquiv.symm.toRingHom))).hom :=
    s3_isLocalHom_of_field _
  have h2 := (SpecToEquivOfLocalRing M.C M.C.functionField).symm.injective
    (a₁ := ⟨_, e3_ffMap θ, i1⟩) (a₂ := ⟨_, _, i2⟩) h1
  obtain ⟨h₁, h3⟩ := SpecToEquivOfLocalRing_eq_iff.mp h2
  have h4 : e3_ffMap θ = CommRingCat.ofHom
      (M.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M.ffEquiv.symm.toRingHom)) := by
    simpa using h3
  rw [h4]
  rfl

p2m_export "AlgebraicCurve.CurveModel" "s3_ffMap_eq_of_fromSpecStalk_comp_eq"
end AlgebraicCurve.CurveModel

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq.AlgebraicCurve"

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (g : SemilinearAut K L)
    (θ : M.C ⟶ M.C) [IsIso θ]
    (hθgen : M.C.fromSpecStalk (genericPoint M.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp ((SemilinearAut.toRingAut g).symm.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (x x' : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hxx' : x'.1.base (IsLocalRing.closedPoint K) = θ.base (x.1.base (IsLocalRing.closedPoint K))) :
    M.pointEquivPlace x' = g • M.pointEquivPlace x := by
  have hff := M.s3_ffMap_eq_of_fromSpecStalk_comp_eq θ (SemilinearAut.toRingAut g) hθgen
  refine Place.ext ?_
  rw [SemilinearAut.smul_toValuationSubring]

  have hmem : θ.base (x.1.base (IsLocalRing.closedPoint K)) ∈ closedPoints M.C :=
    hxx' ▸ (pointEquivClosedPoint M.toBase x').2
  have hpt : pointEquivClosedPoint M.toBase x' = ⟨θ.base (x.1.base (IsLocalRing.closedPoint K)), hmem⟩ :=
    Subtype.ext hxx'
  have r₂ := M.range_stalk_eq ⟨θ.base (x.1.base (IsLocalRing.closedPoint K)), hmem⟩
  have r₁ := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
  have halg := M.s3_ffMap_algebraMap_stalk θ (x.1.base (IsLocalRing.closedPoint K))
  simp only [CurveModel.pointEquivPlace_apply]
  rw [hpt]
  ext f
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def]
  constructor
  · intro hf
    have hf' : f ∈ (M.placeOfPoint ⟨θ.base (x.1.base (IsLocalRing.closedPoint K)), hmem⟩).toValuationSubring.toSubring := hf
    rw [← r₂] at hf'
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp hf'
    have key : (SemilinearAut.toRingAut g).symm (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) =
        M.ffEquiv.symm (algebraMap _ M.C.functionField
          (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s)) := by
      apply M.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply, ← halg, hff]
    show (SemilinearAut.toRingAut g).symm (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) ∈
      (M.placeOfPoint (pointEquivClosedPoint M.toBase x)).toValuationSubring
    rw [key, ← ValuationSubring.mem_toSubring, ← r₁]
    exact ⟨_, rfl⟩
  · intro hf
    have hf' : (SemilinearAut.toRingAut g).symm f ∈
        (M.placeOfPoint (pointEquivClosedPoint M.toBase x)).toValuationSubring.toSubring := hf
    rw [← r₁] at hf'
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hf'
    obtain ⟨s, rfl⟩ : ∃ s : M.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint K))),
        θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s = t :=
      ⟨inv (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K))) t, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have h5 : (SemilinearAut.toRingAut g).symm (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) =
        M.ffEquiv.symm (algebraMap _ M.C.functionField
          (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s)) := by
      apply M.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply, ← halg, hff]
    have key : f = M.ffEquiv.symm (algebraMap _ M.C.functionField s) :=
      (SemilinearAut.toRingAut g).symm.injective (ht.symm.trans h5.symm)
    rw [key]
    show M.ffEquiv.symm (algebraMap _ M.C.functionField s) ∈
      (M.placeOfPoint ⟨θ.base (x.1.base (IsLocalRing.closedPoint K)), hmem⟩).toValuationSubring
    rw [← ValuationSubring.mem_toSubring, ← r₂]
    exact ⟨s, rfl⟩

end E3

end S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq (solution)
