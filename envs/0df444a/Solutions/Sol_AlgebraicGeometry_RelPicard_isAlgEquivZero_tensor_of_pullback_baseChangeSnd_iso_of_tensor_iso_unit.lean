-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2e4d55dd-619b-5bcf-aab3-2d7c2684e3d4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard"

theorem solution
    {k : Type u} [Field k] {K : Type u} [Field K] (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X V : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType hV] [GeometricallyIntegral hV]
    (F : (pullback x (hV ≫ κ)).Modules) (hF : Scheme.Modules.IsInvertible F)
    (v₀ v₁ : Spec (CommRingCat.of K) ⟶ V) (hv₀ : v₀ ≫ hV = 𝟙 _) (hv₁ : v₁ ≫ hV = 𝟙 _)
    (A B P : (pullback x κ).Modules)
    (eA : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₀, by rw [← Category.assoc, hv₀, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ A)
    (eB : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₁, by rw [← Category.assoc, hv₁, Category.id_comp]⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F ≅ B)
    (hP : Scheme.Modules.IsInvertible P) (eP : A ⊗ P ≅ 𝟙_ (pullback x κ).Modules) :
    IsAlgEquivZero (pullback.snd x κ) (B ⊗ P) := by

  let Q : pullback (pullback.snd x κ) hV ≅ pullback x (hV ≫ κ) := pullbackLeftPullbackSndIso x κ hV

  have hvκ : ∀ (v : Spec (CommRingCat.of K) ⟶ V), v ≫ hV = 𝟙 _ → v ≫ hV ≫ κ = κ := fun v hv => by
    rw [← Category.assoc, hv, Category.id_comp]

  have sqF : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV) ≫ Q.hom =
        pullback.fst (pullback.snd x κ) (𝟙 _) ≫ baseChangeSnd x (⟨v, hvκ v hv⟩ : SchemeHomOver κ (hV ≫ κ)) := by
    intro v hv
    apply pullback.hom_ext
    · simp only [Q, baseChangeSnd, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.comp_id]
    · simp only [Q, baseChangeSnd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd,
        pullback.lift_snd_assoc]
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]
  have sqP : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV) ≫ pullback.fst (pullback.snd x κ) hV =
        pullback.fst (pullback.snd x κ) (𝟙 _) := by
    intro v hv
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]

  have isoF : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV))).obj
        ((Scheme.Modules.pullback Q.hom).obj F) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) (𝟙 _))).obj
          ((Scheme.Modules.pullback (baseChangeSnd x (⟨v, hvκ v hv⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F)) :=
    fun v hv => ⟨(Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr (sqF v hv)).app F ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F).symm⟩
  have isoP : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV))).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) hV)).obj P) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) (𝟙 _))).obj P) :=
    fun v hv => ⟨(Scheme.Modules.pullbackComp _ _).app P ≪≫ (Scheme.Modules.pullbackCongr (sqP v hv)).app P⟩

  refine ⟨V, hV, inferInstance, inferInstance,
    (Scheme.Modules.pullback Q.hom).obj F ⊗ (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) hV)).obj P,
    (hF.pullback _).tensor (hP.pullback _), ⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩, ⟨?_⟩, ⟨?_⟩⟩
  ·
    exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((isoF v₀ hv₀).some ≪≫ (Scheme.Modules.pullback _).mapIso eA) ⊗ᵢ (isoP v₀ hv₀).some) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ A P).symm ≪≫ (Scheme.Modules.pullback _).mapIso eP ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  ·
    exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((isoF v₁ hv₁).some ≪≫ (Scheme.Modules.pullback _).mapIso eB) ⊗ᵢ (isoP v₁ hv₁).some) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ B P).symm

end S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit (solution)
