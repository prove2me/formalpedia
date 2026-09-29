-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_map_cocycle_of_pullback_section_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1139fae9-623a-5ab7-b03f-61b56139fc90

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace BenchQFA

p2m_open "AlgebraicGeometry.Scheme.Modules"

section sec

variable {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
  {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
  (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
  (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
  (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
  (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
  (hq : q₁ ≫ p = q₂ ≫ p)
  (e : Spec (CommRingCat.of S) ⟶ T) (e' : Spec (CommRingCat.of S') ⟶ T') (he' : e' ≫ t' = 𝟙 _)
  (hpe : e' ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ e)

noncomputable def eSec : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ T'' :=
  hq₁.lift (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ e') (𝟙 _)
    (by rw [Category.assoc, he', Category.comp_id, Category.id_comp])

omit hp hq₂ hq hpe in
theorem eSec_q₁ : eSec t' t'' q₁ hq₁ e' he' ≫ q₁ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ e' :=
  hq₁.lift_fst _ _ _

omit hp hq₂ hq hpe in
theorem eSec_t'' : eSec t' t'' q₁ hq₁ e' he' ≫ t'' = 𝟙 _ := hq₁.lift_snd _ _ _

include hp hq₂ hq hpe in
theorem eSec_q₂ : eSec t' t'' q₁ hq₁ e' he' ≫ q₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ e' := by
  have hσ : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S S')) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S S')) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')).w
  apply hp.hom_ext
  · rw [Category.assoc, ← hq, ← Category.assoc, eSec_q₁, Category.assoc, hpe, Category.assoc, hpe,
      ← Category.assoc, ← Category.assoc, hσ]
  · rw [Category.assoc, hq₂.w, ← Category.assoc, eSec_t'', Category.id_comp, Category.assoc, he', Category.comp_id]

end sec

section norm

noncomputable def normIso {B A Y₂ T₂ : Scheme.{u}} (e : B ⟶ A) (ι₂ : Y₂ ⟶ A) (ε₂ : T₂ ⟶ Y₂) (p₂ : T₂ ⟶ B)
    (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e) (X : A.Modules) (hXe : (Scheme.Modules.pullback e).obj X ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Scheme.Modules.pullback ε₂).obj ((Scheme.Modules.pullback ι₂).obj X) ≅ SheafOfModules.unit T₂.ringCatSheaf :=
  (pullbackComp ε₂ ι₂).app X ≪≫ (pullbackCongr hp₂).app X ≪≫ ((pullbackComp p₂ e).app X).symm ≪≫
    (Scheme.Modules.pullback p₂).mapIso hXe ≪≫ Scheme.Modules.pullbackUnitIso p₂

theorem normIso_congr {B A Y₂ T₂ : Scheme.{u}} (e : B ⟶ A) (ι₂ : Y₂ ⟶ A) (ε₂ : T₂ ⟶ Y₂) {p₂ p₂' : T₂ ⟶ B}
    (h : p₂ = p₂') (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e) (hp₂' : ε₂ ≫ ι₂ = p₂' ≫ e) (X : A.Modules)
    (hXe : (Scheme.Modules.pullback e).obj X ≅ SheafOfModules.unit B.ringCatSheaf) :
    normIso e ι₂ ε₂ p₂ hp₂ X hXe = normIso e ι₂ ε₂ p₂' hp₂' X hXe := by
  subst h; rfl

end norm

theorem main
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (hΓ'' : Function.Surjective (t''.appTop).hom)
    (e : Spec (CommRingCat.of S) ⟶ T) (he : e ≫ t = 𝟙 _)
    (e' : Spec (CommRingCat.of S') ⟶ T') (he' : e' ≫ t' = 𝟙 _)
    (hpe : e' ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ e)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (τL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (τM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (α : (Scheme.Modules.pullback p).obj L ≅ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback e').map α.hom =
      ((Scheme.Modules.pullbackComp e' p).app L ≪≫ (Scheme.Modules.pullbackCongr hpe).app L ≪≫
        ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app L).symm ≪≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S S')))).mapIso (τL ≪≫ τM.symm) ≪≫
        (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app M ≪≫
        ((Scheme.Modules.pullbackCongr hpe).app M).symm ≪≫ ((Scheme.Modules.pullbackComp e' p).app M).symm).hom) :
    (Scheme.Modules.pullback q₁).map α.hom ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α.hom := by

  let σ := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let σL := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))
  let σR := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)
  have hσ : σL ≫ σ = σR ≫ σ :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')).w

  let e'' := eSec t' t'' q₁ hq₁ e' he'
  have he₁ : e'' ≫ q₁ = σL ≫ e' := eSec_q₁ t' t'' q₁ hq₁ e' he'
  have he₂ : e'' ≫ q₂ = σR ≫ e' := eSec_q₂ t t' p hp t'' q₁ q₂ hq₁ hq₂ hq e e' he' hpe
  have het : e'' ≫ t'' = 𝟙 _ := eSec_t'' t' t'' q₁ hq₁ e' he'
  have hp₂L : e'' ≫ (q₁ ≫ p) = (σL ≫ σ) ≫ e := by
    rw [← Category.assoc, he₁, Category.assoc, hpe, Category.assoc]
  have hp₂R : e'' ≫ (q₁ ≫ p) = (σR ≫ σ) ≫ e := by
    rw [hq, ← Category.assoc, he₂, Category.assoc, hpe, Category.assoc]

  have hφ : (Scheme.Modules.pullback e').map α.hom =
      ((pullbackComp e' p).app L ≪≫ (pullbackCongr hpe).app L ≪≫ ((pullbackComp σ e).app L).symm ≪≫
          (Scheme.Modules.pullback σ).mapIso τL ≪≫ Scheme.Modules.pullbackUnitIso σ).hom ≫
        ((pullbackComp e' p).app M ≪≫ (pullbackCongr hpe).app M ≪≫ ((pullbackComp σ e).app M).symm ≪≫
          (Scheme.Modules.pullback σ).mapIso τM ≪≫ Scheme.Modules.pullbackUnitIso σ).inv := by
    rw [hα, ← Iso.symm_hom, ← Iso.trans_hom]
    congr 1
    simp only [Functor.comp_obj, Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      Iso.self_symm_id_assoc]
    rfl

  have R1 := AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
    e p (q₁ ≫ p) e' σ hpe e'' (σL ≫ σ) hp₂L q₁ rfl σL he₁ rfl L M τL τM α hφ
  have R2 := AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
    e p (q₁ ≫ p) e' σ hpe e'' (σR ≫ σ) hp₂R q₂ hq.symm σR he₂ rfl L M τL τM α hφ

  have hN : ∀ (X : T.Modules) (hXe : (Scheme.Modules.pullback e).obj X ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf),
      ((pullbackComp e'' (q₁ ≫ p)).app X ≪≫ (pullbackCongr hp₂L).app X ≪≫ ((pullbackComp (σL ≫ σ) e).app X).symm ≪≫
        (Scheme.Modules.pullback (σL ≫ σ)).mapIso hXe ≪≫ Scheme.Modules.pullbackUnitIso (σL ≫ σ)) =
      ((pullbackComp e'' (q₁ ≫ p)).app X ≪≫ (pullbackCongr hp₂R).app X ≪≫ ((pullbackComp (σR ≫ σ) e).app X).symm ≪≫
        (Scheme.Modules.pullback (σR ≫ σ)).mapIso hXe ≪≫ Scheme.Modules.pullbackUnitIso (σR ≫ σ)) :=
    fun X hXe => normIso_congr e (q₁ ≫ p) e'' hσ hp₂L hp₂R X hXe

  let γ₁ : (Scheme.Modules.pullback (q₁ ≫ p)).obj L ≅ (Scheme.Modules.pullback (q₁ ≫ p)).obj M :=
    ((pullbackComp q₁ p).app L ≪≫ (pullbackCongr (rfl : q₁ ≫ p = q₁ ≫ p)).app L).symm ≪≫
      (Scheme.Modules.pullback q₁).mapIso α ≪≫ ((pullbackComp q₁ p).app M ≪≫ (pullbackCongr (rfl : q₁ ≫ p = q₁ ≫ p)).app M)
  let γ₂ : (Scheme.Modules.pullback (q₁ ≫ p)).obj L ≅ (Scheme.Modules.pullback (q₁ ≫ p)).obj M :=
    ((pullbackComp q₂ p).app L ≪≫ (pullbackCongr hq.symm).app L).symm ≪≫
      (Scheme.Modules.pullback q₂).mapIso α ≪≫ ((pullbackComp q₂ p).app M ≪≫ (pullbackCongr hq.symm).app M)
  have hγ : γ₁ = γ₂ := by
    apply AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop
      t'' e'' het hΓ'' _ _ (hL.pullback (q₁ ≫ p))
    show (Scheme.Modules.pullback e'').map γ₁.hom = (Scheme.Modules.pullback e'').map γ₂.hom
    rw [R1, R2, hN L τL, hN M τM]

  have hq₁α : (Scheme.Modules.pullback q₁).mapIso α =
      ((pullbackComp q₁ p).app L ≪≫ (pullbackCongr (rfl : q₁ ≫ p = q₁ ≫ p)).app L) ≪≫ γ₂ ≪≫
        ((pullbackComp q₁ p).app M ≪≫ (pullbackCongr (rfl : q₁ ≫ p = q₁ ≫ p)).app M).symm := by
    rw [← hγ]; simp [γ₁]
  have cL : ∀ (X : T.Modules) {a b : T'' ⟶ T} (h : a = b),
      (pullbackCongr h).app X = eqToIso (by rw [h]) := by
    intro X a b h; subst h; rfl
  have es : ∀ {X Y : T''.Modules} (h : X = Y), (eqToIso h).symm = eqToIso h.symm := by
    intro X Y h; cases h; rfl
  have et : ∀ {X Y Z W : T''.Modules} (h₁ : X = Y) (h₂ : Y = Z) (γ : Z ≅ W),
      eqToIso h₁ ≪≫ eqToIso h₂ ≪≫ γ = eqToIso (h₁.trans h₂) ≪≫ γ := by
    intro X Y Z W h₁ h₂ γ; cases h₁; cases h₂; simp
  have er : ∀ {X W : T''.Modules} (h : X = X) (γ : X ≅ W), eqToIso h ≪≫ γ = γ := by
    intro X W h γ; simp
  have key : (Scheme.Modules.pullback q₁).mapIso α ≪≫
      ((pullbackComp q₁ p).app M ≪≫ (pullbackCongr hq).app M ≪≫ ((pullbackComp q₂ p).app M).symm) =
      ((pullbackComp q₁ p).app L ≪≫ (pullbackCongr hq).app L ≪≫ ((pullbackComp q₂ p).app L).symm) ≪≫
        (Scheme.Modules.pullback q₂).mapIso α := by
    rw [hq₁α]
    simp only [Functor.comp_obj, γ₂, cL, eqToIso_refl, Iso.trans_refl, Iso.refl_trans, Iso.trans_symm, Iso.symm_symm_eq,
      Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id, Iso.self_symm_id,
      es, et, er]
  have := congrArg Iso.hom key
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] at this
  exact this

end BenchQFA

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    (hΓ'' : Function.Surjective (t''.appTop).hom)
    (e : Spec (CommRingCat.of S) ⟶ T) (he : e ≫ t = 𝟙 _)
    (e' : Spec (CommRingCat.of S') ⟶ T') (he' : e' ≫ t' = 𝟙 _)
    (hpe : e' ≫ p = Spec.map (CommRingCat.ofHom (algebraMap S S')) ≫ e)
    (L M : T.Modules) (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (τL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (τM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)
    (α : (Scheme.Modules.pullback p).obj L ≅ (Scheme.Modules.pullback p).obj M)
    (hα : (Scheme.Modules.pullback e').map α.hom =
      ((Scheme.Modules.pullbackComp e' p).app L ≪≫ (Scheme.Modules.pullbackCongr hpe).app L ≪≫
        ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app L).symm ≪≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap S S')))).mapIso (τL ≪≫ τM.symm) ≪≫
        (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap S S'))) e).app M ≪≫
        ((Scheme.Modules.pullbackCongr hpe).app M).symm ≪≫ ((Scheme.Modules.pullbackComp e' p).app M).symm).hom) :
    (Scheme.Modules.pullback q₁).map α.hom ≫ ((Scheme.Modules.pullbackComp q₁ p).app M).hom ≫
        ((Scheme.Modules.pullbackCongr hq).app M).hom ≫ ((Scheme.Modules.pullbackComp q₂ p).app M).inv =
      ((Scheme.Modules.pullbackComp q₁ p).app L).hom ≫ ((Scheme.Modules.pullbackCongr hq).app L).hom ≫
        ((Scheme.Modules.pullbackComp q₂ p).app L).inv ≫ (Scheme.Modules.pullback q₂).map α.hom :=
  BenchQFA.main t t' p hp t'' q₁ q₂ hq₁ hq₂ hq hΓ'' e he e' he' hpe L M hL hM τL τM α hα

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_map_cocycle_of_pullback_section_map_eq (solution)
