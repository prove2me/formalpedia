-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_pullback_map_eq_zero_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0837a7fd-4ae2-5010-abd8-7f8313b0f23d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_app_injective_and_exists_of_app_pullback_eq_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Spec Scheme Scheme.Modules.restrictFunctor Scheme.Modules.restrictFunctorIsoPullback IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.comp_apply Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced"
namespace Vanish2
p2m_open "AlgebraicGeometry"

theorem app_apply_eq_zero_of_pullback_map_eq_zero {Z V : Scheme.{u}} (g : Z ⟶ V) {A : V.Modules}
    (τ : A ⟶ (SheafOfModules.unit V.ringCatSheaf : V.Modules))
    (h : (Scheme.Modules.pullback g).map τ = 0)
    (W : V.Opens) (a : Γ(A, W)) : g.app W (τ.app W a) = 0 := by
  have key : τ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom = 0 := by
    have nat := (SheafOfModules.pullbackPushforwardAdjunction g.toRingCatSheafHom).homEquiv_naturality_left τ
      (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit] at nat
    have h' : (SheafOfModules.pullback g.toRingCatSheafHom).map τ = 0 := h
    rw [h', zero_comp, Adjunction.homEquiv_apply, Functor.map_zero] at nat
    have h__af := nat.symm
    simp at h__af
    exact h__af
  have := congrArg (fun φ : A ⟶ _ => (φ.val.app (op W)) a) key
  simp [SheafOfModules.unitToPushforwardObjUnit_val_app_apply] at this
  exact this

end AlgebraicGeometry.Vanish2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme.Hom.image_preimage_le Spec Scheme Scheme.Modules.restrictFunctor Scheme.Modules.restrictFunctorIsoPullback IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.comp_apply Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.Hom.app_smul Modules.Hom.zero_app ringCatSheaf Modules.pullback Hom Γ Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.image_preimage_le Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules.pullbackCongr Modules Opens restrict Hom.comp_apply Modules.pullbackComp Modules.IsInvertible" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul Hom.zero_app pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback pullbackCongr isSheaf pullbackPushforwardAdjunction restrict pullbackComp IsInvertible" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

theorem AlgebraicGeometry.Scheme.Modules.pullback_morphismRestrict_map_restrictFunctor_map_eq_zero
    {X Y : Scheme.{u}} (i : Y ⟶ X) (V : X.Opens) {A B : X.Modules} (σ : A ⟶ B)
    (h : (Scheme.Modules.pullback i).map σ = 0) :
    (Scheme.Modules.pullback (i ∣_ V)).map ((Scheme.Modules.restrictFunctor V.ι).map σ) = 0 := by

  let N : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (i ∣_ V) ≅
      Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback (i ⁻¹ᵁ V).ι :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) (Scheme.Modules.pullback (i ∣_ V)) ≪≫
      Scheme.Modules.pullbackComp (i ∣_ V) V.ι ≪≫
      Scheme.Modules.pullbackCongr (morphismRestrict_ι i V) ≪≫
      (Scheme.Modules.pullbackComp (i ⁻¹ᵁ V).ι i).symm
  have hG : (Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback (i ⁻¹ᵁ V).ι).map σ = 0 := by
    show (Scheme.Modules.pullback (i ⁻¹ᵁ V).ι).map ((Scheme.Modules.pullback i).map σ) = 0
    rw [h, Functor.map_zero]
  have nat := N.hom.naturality σ
  rw [hG, comp_zero] at nat
  have hF : (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (i ∣_ V)).map σ = 0 :=
    (cancel_mono (N.hom.app B)).mp (by rw [nat, zero_comp])
  exact hF

open AlgebraicGeometry.Vanish2 in

theorem solution
    {X Y₁ Y₂ : Scheme.{u}} [IsReduced X] (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ L)
    (h₁ : (Scheme.Modules.pullback i₁).map σ = 0) (h₂ : (Scheme.Modules.pullback i₂).map σ = 0) :
    σ = 0 := by
  classical

  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let σ' : O ⟶ L := σ
  have h₁' : (Scheme.Modules.pullback i₁).map σ' = 0 := h₁
  have h₂' : (Scheme.Modules.pullback i₂).map σ' = 0 := h₂

  have loc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ∀ W' : (V : Scheme.{u}).Opens, σ'.app (V.ι ''ᵁ W') (1 : Γ(X, V.ι ''ᵁ W')) = 0 := by
    intro x
    obtain ⟨V, hxV, ⟨e⟩⟩ := hL.exists_trivialization x
    refine ⟨V, hxV, fun W' => ?_⟩

    let e' : (Scheme.Modules.restrictFunctor V.ι).obj L ≅
        (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules) :=
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L ≪≫ e
    let τ : (Scheme.Modules.restrictFunctor V.ι).obj O ⟶
        (SheafOfModules.unit (V : Scheme.{u}).ringCatSheaf : (V : Scheme.{u}).Modules) :=
      (Scheme.Modules.restrictFunctor V.ι).map σ' ≫ e'.hom
    have hτ : ∀ {Y : Scheme.{u}} (i : Y ⟶ X), (Scheme.Modules.pullback i).map σ' = 0 →
        (Scheme.Modules.pullback (i ∣_ V)).map τ = 0 := by
      intro Y i hi
      show (Scheme.Modules.pullback (i ∣_ V)).map (_ ≫ _) = 0
      rw [Functor.map_comp, Scheme.Modules.pullback_morphismRestrict_map_restrictFunctor_map_eq_zero i V σ' hi,
        zero_comp]
    have k₁ := app_apply_eq_zero_of_pullback_map_eq_zero (i₁ ∣_ V) τ (hτ i₁ h₁') W' (1 : Γ(X, V.ι ''ᵁ W'))
    have k₂ := app_apply_eq_zero_of_pullback_map_eq_zero (i₂ ∣_ V) τ (hτ i₂ h₂') W' (1 : Γ(X, V.ι ''ᵁ W'))

    have hcovV : Set.range (i₁ ∣_ V).base ∪ Set.range (i₂ ∣_ V).base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      have hv : (V.ι.base v) ∈ Set.range i₁.base ∪ Set.range i₂.base := by rw [hcover]; trivial
      rcases hv with ⟨y, hy⟩ | ⟨y, hy⟩
      · left
        have hyV : y ∈ i₁ ⁻¹ᵁ V := by
          show i₁.base y ∈ V
          rw [hy]; exact v.2
        refine ⟨⟨y, hyV⟩, ?_⟩
        apply V.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact hy
      · right
        have hyV : y ∈ i₂ ⁻¹ᵁ V := by
          show i₂.base y ∈ V
          rw [hy]; exact v.2
        refine ⟨⟨y, hyV⟩, ?_⟩
        apply V.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact hy
    have inj := (AlgebraicGeometry.IsClosedImmersion.app_injective_and_exists_of_app_pullback_eq_of_isReduced
      (i₁ ∣_ V) (i₂ ∣_ V) hcovV W').1
    have hf : τ.app W' (1 : Γ(X, V.ι ''ᵁ W')) = 0 := by
      apply inj
      refine Prod.ext ?_ ?_
      · exact k₁.trans (map_zero ((i₁ ∣_ V).app W').hom).symm
      · exact k₂.trans (map_zero ((i₂ ∣_ V).app W').hom).symm

    have hinj : Function.Injective (e'.hom.app W') :=
      (ConcreteCategory.bijective_of_isIso (e'.hom.app W')).1
    apply hinj
    change τ.app W' (1 : Γ(X, V.ι ''ᵁ W')) = e'.hom.app W' 0
    rw [hf]
    exact (map_zero _).symm

  have hall : ∀ U : X.Opens, σ'.app U (1 : Γ(X, U)) = 0 := by
    intro U
    apply TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ U
    intro x hxU
    obtain ⟨V, hxV, hV⟩ := loc x

    have hW : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) ≤ U := Scheme.Hom.image_preimage_le V.ι U
    have hxW : x ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ U) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact ⟨by simpa using hxV, hxU⟩
    rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hW) x hxW,
      ← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hW) x hxW]
    congr 1
    rw [map_zero]

    have nat := congrArg (fun φ => (ModuleCat.Hom.hom φ) (show Γ(O, U) from (1 : Γ(X, U))))
      (σ'.val.naturality (homOfLE hW).op)
    change σ'.app (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) (X.presheaf.map (homOfLE hW).op (1 : Γ(X, U))) =
      L.presheaf.map (homOfLE hW).op (σ'.app U (1 : Γ(X, U))) at nat
    rw [map_one] at nat
    change L.presheaf.map (homOfLE hW).op (σ'.app U (1 : Γ(X, U))) = 0
    rw [← nat]
    exact hV _

  show σ' = 0
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rw [Scheme.Modules.Hom.zero_app]
  have e1 : a = (show Γ(X, U) from a) • (show Γ(O, U) from (1 : Γ(X, U))) :=
    (mul_one (show Γ(X, U) from a)).symm
  rw [e1, Scheme.Modules.Hom.app_smul, hall U, smul_zero]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_pullback_map_eq_zero_of_isReduced (solution)
