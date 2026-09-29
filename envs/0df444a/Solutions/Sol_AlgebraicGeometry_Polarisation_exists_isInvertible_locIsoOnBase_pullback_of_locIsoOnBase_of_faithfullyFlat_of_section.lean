-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b8a4f5fc-50d9-57f2-b456-942f62b96811

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective
import Theorems.Thm_AlgebraicGeometry_Polarisation_cocycle_of_rigidifiedIso
import Theorems.Thm_AlgebraicGeometry_bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_rigidified_locIsoOnBase_of_section
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

namespace L4LDL

theorem bij_of_isPullback {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra S T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤)))
    (T : Type u) [CommRing T] [Algebra S T] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of T)) (gX : X ⟶ A)
    (hX : IsPullback gX fX f (Spec.map (CommRingCat.ofHom (algebraMap S T)))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ fX.appTop).hom := by
  let κ := hX.isoPullback
  have hκ : κ.hom ≫ pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T) = fX := hX.isoPullback_hom_snd
  have h0 := hH0 T
  change Function.Bijective (((Scheme.ΓSpecIso (.of T)).inv ≫
    (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)).appLE ⊤ ⊤ le_top).hom) at h0
  have happ : (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)).appLE ⊤ ⊤ le_top =
      (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)).appTop := Scheme.Hom.appLE_eq_app _
  rw [happ] at h0
  have e1 : κ.hom.appTop ≫ κ.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  have e2 : κ.inv.appTop ≫ κ.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  let ι : Γ(pullback f (Scheme.TwoAffineOpenCover.specMap S T), ⊤) ≅ Γ(X, ⊤) := ⟨κ.hom.appTop, κ.inv.appTop, e1, e2⟩
  haveI : IsIso ι.hom := ι.isIso_hom
  have hfac : (((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ fX.appTop).hom : T → _) =
      ι.hom.hom ∘ ((Scheme.ΓSpecIso (.of T)).inv ≫ (pullback.snd f (Scheme.TwoAffineOpenCover.specMap S T)).appTop).hom := by
    rw [← hκ, Scheme.Hom.comp_appTop]; rfl
  rw [hfac]
  exact (ConcreteCategory.bijective_of_isIso ι.hom).comp h0

end L4LDL

open L4LDL in
theorem solution
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {A A' A'' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra R T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)))
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (f' : A' ⟶ Spec (CommRingCat.of R')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (R' ⊗[R] R'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (hga : a₁ ≫ g = a₂ ≫ g)
    (𝓛' : A'.Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (hdd : LocIsoOnBase f'' ((Scheme.Modules.pullback a₁).obj 𝓛') ((Scheme.Modules.pullback a₂).obj 𝓛')) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ LocIsoOnBase f' ((Scheme.Modules.pullback g).obj 𝓛) 𝓛' := by
  classical

  let iL : R' →+* (R' ⊗[R] R') := (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R')).toRingHom
  let iR : R' →+* (R' ⊗[R] R') := (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R')).toRingHom
  let m₁₂ : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R')) := (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R'))).toRingHom
  let m₁₃ : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R')) := (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R'))).toRingHom
  let m₂₃ : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R')) := (Algebra.TensorProduct.includeRight : (R' ⊗[R] R') →ₐ[R] (R' ⊗[R] (R' ⊗[R] R'))).toRingHom
  let ι₁ := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let ι₂ := Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))
  let ι₃ := Spec.map (CommRingCat.ofHom (S := (R' ⊗[R] (R' ⊗[R] R'))) (algebraMap R (R' ⊗[R] (R' ⊗[R] R'))))
  have hiL : iL.comp (algebraMap R R') = algebraMap R (R' ⊗[R] R') := (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R')).comp_algebraMap
  have hiR : iR.comp (algebraMap R R') = algebraMap R (R' ⊗[R] R') := (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R')).comp_algebraMap
  have hm₁₂ : m₁₂.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R')) :=
    (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R'))).comp_algebraMap
  have hm₁₃ : m₁₃.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R')) :=
    (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R'))).comp_algebraMap
  have hm₂₃ : m₂₃.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R')) :=
    (Algebra.TensorProduct.includeRight : (R' ⊗[R] R') →ₐ[R] (R' ⊗[R] (R' ⊗[R] R'))).comp_algebraMap

  have hι₂ : Spec.map (CommRingCat.ofHom iL) ≫ ι₁ = ι₂ := by
    change Spec.map (CommRingCat.ofHom iL) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hiL]
  have H2 : IsPullback (a₁ ≫ g) f'' f ι₂ := by rw [← hι₂]; exact IsPullback.paste_horiz ha₁ hg

  haveI : QuasiCompact f'' := MorphismProperty.of_isPullback H2 inferInstance
  haveI : IsSeparated f'' := MorphismProperty.of_isPullback H2 inferInstance
  haveI : QuasiCompact f' := MorphismProperty.of_isPullback hg inferInstance
  haveI : IsSeparated f' := MorphismProperty.of_isPullback hg inferInstance

  let e' : Spec (CommRingCat.of R') ⟶ A' := hg.lift (ι₁ ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have he'g : e' ≫ g = ι₁ ≫ e := hg.lift_fst _ _ _
  have he'f : e' ≫ f' = 𝟙 _ := hg.lift_snd _ _ _
  let e'' : Spec (CommRingCat.of (R' ⊗[R] R')) ⟶ A'' := H2.lift (ι₂ ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have he''g : e'' ≫ a₁ ≫ g = ι₂ ≫ e := H2.lift_fst _ _ _
  have he''f : e'' ≫ f'' = 𝟙 _ := H2.lift_snd _ _ _
  have he''a₁ : e'' ≫ a₁ = Spec.map (CommRingCat.ofHom iL) ≫ e' := by
    apply hg.hom_ext
    · rw [Category.assoc, he''g, Category.assoc, he'g, ← Category.assoc, hι₂]
    · rw [Category.assoc, ha₁.w, ← Category.assoc, he''f, Category.id_comp, Category.assoc, he'f, Category.comp_id]
  have he''a₂ : e'' ≫ a₂ = Spec.map (CommRingCat.ofHom iR) ≫ e' := by
    apply hg.hom_ext
    · rw [Category.assoc, ← hga, he''g, Category.assoc, he'g, ← Category.assoc]
      change _ = (Spec.map (CommRingCat.ofHom iR) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ e
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hiR]
    · rw [Category.assoc, ha₂.w, ← Category.assoc, he''f, Category.id_comp, Category.assoc, he'f, Category.comp_id]

  obtain ⟨𝓛₁, h𝓛₁, ⟨α⟩, hL⟩ :=
    Scheme.Modules.IsInvertible.exists_isInvertible_rigidified_locIsoOnBase_of_section f' e' he'f 𝓛' h𝓛'
  have hEq2 := LocIsoOnBase.equivalence f''
  have hdd₁ : LocIsoOnBase f'' ((Scheme.Modules.pullback a₁).obj 𝓛₁) ((Scheme.Modules.pullback a₂).obj 𝓛₁) :=
    hEq2.trans (hEq2.trans (hEq2.symm (LocIsoOnBase.pullback_of_isPullback iL ha₁ hL)) hdd) (LocIsoOnBase.pullback_of_isPullback iR ha₂ hL)

  let α₁ : (Scheme.Modules.pullback e'').obj ((Scheme.Modules.pullback a₁).obj 𝓛₁) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R' ⊗[R] R'))).ringCatSheaf :=
    (Scheme.Modules.pullbackComp e'' a₁).app 𝓛₁ ≪≫ (Scheme.Modules.pullbackCongr he''a₁).app 𝓛₁ ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom iL)) e').app 𝓛₁).symm ≪≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom iL))).mapIso α ≪≫ Scheme.Modules.pullbackUnitIso _
  let α₂ : (Scheme.Modules.pullback e'').obj ((Scheme.Modules.pullback a₂).obj 𝓛₁) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (R' ⊗[R] R'))).ringCatSheaf :=
    (Scheme.Modules.pullbackComp e'' a₂).app 𝓛₁ ≪≫ (Scheme.Modules.pullbackCongr he''a₂).app 𝓛₁ ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom iR)) e').app 𝓛₁).symm ≪≫
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom iR))).mapIso α ≪≫ Scheme.Modules.pullbackUnitIso _

  have hH0₂ : ∀ (T' : Type u) [CommRing T'] [Algebra (R' ⊗[R] R') T'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f'' (Scheme.TwoAffineOpenCover.specMap (R' ⊗[R] R') T')) ⊤
      Function.Bijective (algebraMap T' Γ(pullback f'' (Scheme.TwoAffineOpenCover.specMap (R' ⊗[R] R') T'), ⊤)) :=
    fun T' _ _ => AlgebraicGeometry.bijective_algebraMap_sections_pullback_of_isPullback_of_forall_bijective f hH0
      (R' ⊗[R] R') f'' (a₁ ≫ g) H2 T'
  obtain ⟨⟨⟨ψ, hψr⟩⟩, -⟩ :=
    AlgebraicGeometry.Polarisation.nonempty_and_subsingleton_rigidifiedIso_of_locIsoOnBase_of_forall_bijective f'' hH0₂ e'' he''f
      _ _ (h𝓛₁.pullback a₁) (h𝓛₁.pullback a₂) hdd₁ α₁ α₂

  let X3 : Scheme.{u} := pullback f ι₃
  let t₃ : X3 ⟶ Spec (CommRingCat.of (R' ⊗[R] (R' ⊗[R] R'))) := pullback.snd f ι₃
  have hX3 : ∀ (m : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R'))) (hm : m.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R'))),
      IsPullback (pullback.fst f ι₃) t₃ f (Spec.map (CommRingCat.ofHom m) ≫ ι₂) := by
    intro m hm
    have : Spec.map (CommRingCat.ofHom m) ≫ ι₂ = ι₃ := by
      change Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R'))) = Spec.map (CommRingCat.ofHom (S := (R' ⊗[R] (R' ⊗[R] R'))) (algebraMap R (R' ⊗[R] (R' ⊗[R] R'))))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hm]
    rw [this]
    exact IsPullback.of_hasPullback f ι₃

  let bOf : ∀ (m : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R'))) (hm : m.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R'))), X3 ⟶ A'' := fun m hm =>
    H2.lift (pullback.fst f ι₃) (t₃ ≫ Spec.map (CommRingCat.ofHom m)) (by rw [(hX3 m hm).w, Category.assoc])
  have hbOf : ∀ (m : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R'))) (hm : m.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R'))),
      IsPullback (bOf m hm) t₃ f'' (Spec.map (CommRingCat.ofHom m)) := fun m hm => IsPullback.of_right' (hX3 m hm) H2
  have hbOf_g : ∀ (m : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R'))) (hm : m.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R'))),
      bOf m hm ≫ a₁ ≫ g = pullback.fst f ι₃ := fun m hm => H2.lift_fst _ _ _
  have hbOf_f : ∀ (m : (R' ⊗[R] R') →+* (R' ⊗[R] (R' ⊗[R] R'))) (hm : m.comp (algebraMap R (R' ⊗[R] R')) = algebraMap R (R' ⊗[R] (R' ⊗[R] R'))),
      bOf m hm ≫ f'' = t₃ ≫ Spec.map (CommRingCat.ofHom m) := fun m hm => H2.lift_snd _ _ _
  let b₁₂ := bOf m₁₂ hm₁₂
  let b₁₃ := bOf m₁₃ hm₁₃
  let b₂₃ := bOf m₂₃ hm₂₃

  have r₁ : m₁₂.comp iL = m₁₃.comp iL := by
    change ((Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeLeft).toRingHom =
      ((Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeLeft).toRingHom
    rw [Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeLeft]
  have r₂ : m₁₂.comp iR = m₂₃.comp iL := by
    change ((Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : R' →ₐ[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeRight).toRingHom =
      ((Algebra.TensorProduct.includeRight : (R' ⊗[R] R') →ₐ[R] (R' ⊗[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeLeft).toRingHom
    rw [Algebra.TensorProduct.map_comp_includeRight]
  have r₃ : m₁₃.comp iR = m₂₃.comp iR := by
    change ((Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : R' →ₐ[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeRight).toRingHom =
      ((Algebra.TensorProduct.includeRight : (R' ⊗[R] R') →ₐ[R] (R' ⊗[R] (R' ⊗[R] R'))).comp
        Algebra.TensorProduct.includeRight).toRingHom
    rw [Algebra.TensorProduct.map_comp_includeRight]
  have specComp : ∀ {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] (φ : X →+* Y) (ψ' : Y →+* Z),
      Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ'.comp φ)) := by
    intro X Y Z _ _ _ φ ψ'
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁ := by
    apply hg.hom_ext
    · rw [Category.assoc, hbOf_g m₁₂ hm₁₂, Category.assoc, hbOf_g m₁₃ hm₁₃]
    · rw [Category.assoc, ha₁.w, ← Category.assoc, hbOf_f m₁₂ hm₁₂, Category.assoc, specComp,
        Category.assoc, ha₁.w, ← Category.assoc, hbOf_f m₁₃ hm₁₃, Category.assoc, specComp, r₁]
  have h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁ := by
    apply hg.hom_ext
    · rw [Category.assoc, ← hga, hbOf_g m₁₂ hm₁₂, Category.assoc, hbOf_g m₂₃ hm₂₃]
    · rw [Category.assoc, ha₂.w, ← Category.assoc, hbOf_f m₁₂ hm₁₂, Category.assoc, specComp,
        Category.assoc, ha₁.w, ← Category.assoc, hbOf_f m₂₃ hm₂₃, Category.assoc, specComp, r₂]
  have h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂ := by
    apply hg.hom_ext
    · rw [Category.assoc, ← hga, hbOf_g m₁₃ hm₁₃, Category.assoc, ← hga, hbOf_g m₂₃ hm₂₃]
    · rw [Category.assoc, ha₂.w, ← Category.assoc, hbOf_f m₁₃ hm₁₃, Category.assoc, specComp,
        Category.assoc, ha₂.w, ← Category.assoc, hbOf_f m₂₃ hm₂₃, Category.assoc, specComp, r₃]

  have hψ := AlgebraicGeometry.Polarisation.cocycle_of_rigidifiedIso R' f hH0 e he f' g hg f'' a₁ a₂ ha₁ ha₂ hga
    e' he'g he'f e'' he''a₁ he''a₂ he''f 𝓛₁ h𝓛₁ α ψ hψr t₃ (pullback.fst f ι₃) (IsPullback.of_hasPullback f ι₃)
    b₁₂ b₁₃ b₂₃ (hbOf_g m₁₂ hm₁₂) (hbOf_g m₁₃ hm₁₃) (hbOf_g m₂₃ hm₂₃) (hbOf_f m₁₂ hm₁₂) (hbOf_f m₁₃ hm₁₃) (hbOf_f m₂₃ hm₂₃) h₁ h₂ h₃

  obtain ⟨𝓛, h𝓛, ⟨eL⟩⟩ :=
    Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback R' A' f' 𝓛₁ h𝓛₁ A'' f'' a₁ a₂ ha₁ ha₂
      X3 t₃ b₁₂ b₁₃ b₂₃ (hbOf m₁₂ hm₁₂) (hbOf m₁₃ hm₁₃) (hbOf m₂₃ hm₂₃) h₁ h₂ h₃ ψ hψ A f g hg hga
  have hEq1 := LocIsoOnBase.equivalence f'
  exact ⟨𝓛, h𝓛, hEq1.trans (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eL⟩⟩) (hEq1.symm hL)⟩

end S_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_isInvertible_locIsoOnBase_pullback_of_locIsoOnBase_of_faithfullyFlat_of_section (solution)
