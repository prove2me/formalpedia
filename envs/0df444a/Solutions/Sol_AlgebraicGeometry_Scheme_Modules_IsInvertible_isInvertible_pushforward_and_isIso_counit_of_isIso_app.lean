-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.isInvertible_pushforward_and_isIso_counit_of_isIso_app
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a8aa566a-d83f-5ae3-b5ce-4202e88b240a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforward morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom morphismRestrict_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf isPullback_morphismRestrict Scheme image_morphismRestrict_preimage Scheme.Modules.Hom.isIso_iff_isIso_app Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.preimage_image_eq Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pushforward Modules.pullback Hom Γ Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.isIso_iff_isIso_app Modules.pullbackPushforwardAdjunction Hom.preimage_image_eq Modules Opens homOfLE_ι Opens.opensRange_ι Modules.IsInvertible Modules.Hom.isIso_of_forall_exists_isIso_pullback_map"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom pullbackCongr Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction pullbackComp IsInvertible pullbackUnitIso pullbackTwoSquare baseChangeHom baseChangeHom_counit app_pullbackLocalSection toUnitSection ofUnitSection ofUnitSection_toUnitSection toUnitSection_ofUnitSection ofUnitSection_injective isIso_baseChangeHom_of_isOpenImmersion pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection Hom.isIso_of_forall_exists_isIso_pullback_map"
namespace DescGlob
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section HA

variable {V W : Scheme.{u}} (g : V ⟶ W)

noncomputable abbrev 𝒪 (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

noncomputable def sigma : 𝒪 W ⟶ (pushforward g).obj (𝒪 V) :=
  (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom

theorem sigma_app_apply (U : W.Opens) (r : Γ(W, U)) :
    (sigma g).app U (toUnitSection U r) = toUnitSection (g ⁻¹ᵁ U) (g.app U r) := by
  have h1 := app_pullbackLocalSection g (pullbackUnitIso g).hom (toUnitSection U r)
  have h2 := pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection g U r
  exact (h1.symm.trans h2 :)

theorem bijective_sigma_app (U : W.Opens) (hg : IsIso (g.app U)) :
    Function.Bijective ((sigma g).app U) := by
  have hb : Function.Bijective (g.app U) := ConcreteCategory.bijective_of_isIso (g.app U)
  have key : ∀ a : Γ(𝒪 W, U),
      (sigma g).app U a = toUnitSection (g ⁻¹ᵁ U) (g.app U (ofUnitSection U a)) :=
    fun a => sigma_app_apply g U (ofUnitSection U a)
  constructor
  · intro a b hab
    have h1 : toUnitSection (g ⁻¹ᵁ U) (g.app U (ofUnitSection U a)) =
        toUnitSection (g ⁻¹ᵁ U) (g.app U (ofUnitSection U b)) := by rw [← key, ← key]; exact hab
    have h2 := congrArg (ofUnitSection (g ⁻¹ᵁ U)) h1
    simp only [ofUnitSection_toUnitSection] at h2
    exact ofUnitSection_injective U (hb.1 h2)
  · intro c
    obtain ⟨r, hr⟩ := hb.2 (ofUnitSection (g ⁻¹ᵁ U) c)
    refine ⟨toUnitSection U r, ?_⟩
    rw [sigma_app_apply, hr, toUnitSection_ofUnitSection]

theorem isIso_sigma (hg : ∀ U : W.Opens, IsIso (g.app U)) : IsIso (sigma g) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_sigma_app g U (hg U))

theorem pullback_map_sigma_comp_counit :
    (pullback g).map (sigma g) ≫ (pullbackPushforwardAdjunction g).counit.app (𝒪 V) =
      (pullbackUnitIso g).hom :=
  ((pullbackPushforwardAdjunction g).homEquiv_counit (X := 𝒪 W) (Y := 𝒪 V) (g := sigma g)).symm.trans
    (Equiv.symm_apply_apply ((pullbackPushforwardAdjunction g).homEquiv (𝒪 W) (𝒪 V))
      (pullbackUnitIso g).hom)

theorem isIso_counit_app_unit (hg : ∀ U : W.Opens, IsIso (g.app U)) :
    IsIso ((pullbackPushforwardAdjunction g).counit.app (𝒪 V)) := by
  have w := pullback_map_sigma_comp_counit g
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ (pullback g) (sigma g) (isIso_sigma g hg)) (Iso.isIso_hom _) w

theorem isIso_counit_app_of_iso_unit (hg : ∀ U : W.Opens, IsIso (g.app U)) {N : V.Modules}
    (τ : N ≅ 𝒪 V) : IsIso ((pullbackPushforwardAdjunction g).counit.app N) := by
  have hnat := (pullbackPushforwardAdjunction g).counit.naturality τ.hom

  have i1 : IsIso ((pushforward g ⋙ pullback g).map τ.hom ≫
      (pullbackPushforwardAdjunction g).counit.app (𝒪 V)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (isIso_counit_app_unit g hg)
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ _ τ.hom (Iso.isIso_hom τ)) i1 hnat.symm

noncomputable def pushforwardIsoUnit (hg : ∀ U : W.Opens, IsIso (g.app U)) {N : V.Modules}
    (τ : N ≅ 𝒪 V) : (pushforward g).obj N ≅ 𝒪 W :=
  (pushforward g).mapIso τ ≪≫ (@asIso _ _ _ _ (sigma g) (isIso_sigma g hg)).symm

end HA

section HB

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Opens) (L : Y.Modules)

theorem sq : (f ⁻¹ᵁ W).ι ≫ f = (f ∣_ W) ≫ W.ι := (morphismRestrict_ι f W).symm

theorem isIso_baseChangeHom : IsIso (baseChangeHom (sq f W) L) :=
  isIso_baseChangeHom_of_isOpenImmersion (isPullback_morphismRestrict f W).flip L

theorem isIso_pullbackTwoSquare_app (M : X.Modules) :
    IsIso ((pullbackTwoSquare (sq f W)).natTrans.app M) := by
  change IsIso (((pullbackComp (f ∣_ W) W.ι).hom ≫ (pullbackCongr (sq f W).symm).hom ≫
    (pullbackComp (f ⁻¹ᵁ W).ι f).inv).app M)
  infer_instance

theorem isIso_pullback_map_counit_iff :
    IsIso ((pullback (f ⁻¹ᵁ W).ι).map ((pullbackPushforwardAdjunction f).counit.app L)) ↔
      IsIso ((pullbackPushforwardAdjunction (f ∣_ W)).counit.app ((pullback (f ⁻¹ᵁ W).ι).obj L)) := by
  have key := baseChangeHom_counit (sq f W) L
  have i1 : IsIso ((pullback (f ∣_ W)).map (baseChangeHom (sq f W) L)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_baseChangeHom f W L)
  have i2 := isIso_pullbackTwoSquare_app f W ((pushforward f).obj L)
  constructor
  · intro h
    exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ i1 (@IsIso.comp_isIso _ _ _ _ _ _ _ i2 h) key
  · intro h
    exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ i2 (@IsIso.comp_isIso _ _ _ _ _ _ _ i1 h) key.symm

noncomputable def pullbackPushforwardIso :
    (pullback W.ι).obj ((pushforward f).obj L) ≅
      (pushforward (f ∣_ W)).obj ((pullback (f ⁻¹ᵁ W).ι).obj L) :=
  @asIso _ _ _ _ (baseChangeHom (sq f W) L) (isIso_baseChangeHom f W L)

end HB

section HW

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L : Y.Modules)

theorem isIso_morphismRestrict_app (W : X.Opens) (hO : ∀ V : X.Opens, V ≤ W → IsIso (f.app V))
    (U : W.toScheme.Opens) : IsIso ((f ∣_ W).app U) := by
  rw [morphismRestrict_app]
  have i1 := hO (W.ι ''ᵁ U) (W.ι.image_le_opensRange U |>.trans_eq W.opensRange_ι)
  have i2 : IsIso (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f W U)).op) := by
    rw [eqToHom_op]; infer_instance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2

theorem core
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (∀ V : X.Opens, V ≤ W → IsIso (f.app V)) ∧
      Nonempty ((pullback (f ⁻¹ᵁ W).ι).obj L ≅ SheafOfModules.unit (f ⁻¹ᵁ W).toScheme.ringCatSheaf)) :
    Scheme.Modules.IsInvertible ((pushforward f).obj L) ∧
      IsIso ((pullbackPushforwardAdjunction f).counit.app L) := by
  constructor
  · refine ⟨fun x => ?_⟩
    obtain ⟨W, hxW, hO, ⟨τ⟩⟩ := h x
    exact ⟨W, hxW, ⟨pullbackPushforwardIso f W L ≪≫
      pushforwardIsoUnit (f ∣_ W) (isIso_morphismRestrict_app f W hO) τ⟩⟩
  · apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
    intro y
    obtain ⟨W, hxW, hO, ⟨τ⟩⟩ := h (f.base y)
    refine ⟨f ⁻¹ᵁ W, hxW, ?_⟩
    rw [isIso_pullback_map_counit_iff]
    exact isIso_counit_app_of_iso_unit (f ∣_ W) (isIso_morphismRestrict_app f W hO) τ

end HW

section G1

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (L : Y.Modules)

noncomputable def pullbackIsoUnitOfLE {V V' : Y.Opens} (hle : V ≤ V')
    (τ : (pullback V'.ι).obj L ≅ SheafOfModules.unit V'.toScheme.ringCatSheaf) :
    (pullback V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (pullbackCongr (Y.homOfLE_ι hle).symm).app L ≪≫
    ((pullbackComp (Y.homOfLE hle) V'.ι).app L).symm ≪≫
    (pullback (Y.homOfLE hle)).mapIso τ ≪≫
    pullbackUnitIso (Y.homOfLE hle)

theorem isIso_app_of_le (V : X.Opens) (hV : V ≤ U) : IsIso (f.app V) := by
  obtain ⟨V₁, rfl⟩ : ∃ V₁ : U.toScheme.Opens, U.ι ''ᵁ V₁ = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]⟩
  have h := morphismRestrict_app f U V₁
  have i1 : IsIso ((f ∣_ U).app V₁) := inferInstance
  have i2 : IsIso (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V₁)).op) := by
    rw [eqToHom_op]; infer_instance
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ i2 i1 h.symm

theorem exists_nhd_of_mem_isoLocus (hL : Scheme.Modules.IsInvertible L) {x : X} (hx : x ∈ U) :
    ∃ W : X.Opens, x ∈ W ∧ (∀ V : X.Opens, V ≤ W → IsIso (f.app V)) ∧
      Nonempty ((pullback (f ⁻¹ᵁ W).ι).obj L ≅ SheafOfModules.unit (f ⁻¹ᵁ W).toScheme.ringCatSheaf) := by
  set e : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme := f ∣_ U with he

  set y' : (f ⁻¹ᵁ U).toScheme := (inv e).base (⟨x, hx⟩ : U.toScheme) with hy'
  set y : Y := (f ⁻¹ᵁ U).ι.base y' with hy
  obtain ⟨V', hyV', ⟨τ⟩⟩ := hL.1 y
  let A : (f ⁻¹ᵁ U).toScheme.Opens := (f ⁻¹ᵁ U).ι ⁻¹ᵁ V'
  let B : U.toScheme.Opens := e ''ᵁ A
  refine ⟨U.ι ''ᵁ B, ?_, fun V hV => isIso_app_of_le f U V (hV.trans (U.ι.image_le_opensRange B
    |>.trans_eq U.opensRange_ι)), ⟨pullbackIsoUnitOfLE L ?_ τ⟩⟩
  · refine ⟨⟨x, hx⟩, ⟨y', hyV', ?_⟩, rfl⟩
    change (inv e ≫ e).base (⟨x, hx⟩ : U.toScheme) = _
    rw [IsIso.inv_hom_id]; rfl
  · rw [← image_morphismRestrict_preimage, ← he, Scheme.Hom.preimage_image_eq]
    exact (f ⁻¹ᵁ U).ι.image_preimage_le V'

end G1

end AlgebraicGeometry.Scheme.Modules.DescGlob

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app.AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (hU : IsIso (f ∣_ U))
    {ι : Type v} (W : ι → X.Opens) (hcov : U ⊔ ⨆ i, W i = ⊤)
    (hO : ∀ (i : ι) (V : X.Opens), V ≤ W i → IsIso (f.app V))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hW : ∀ i, Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ (W i)).ι).obj L ≅
      SheafOfModules.unit (f ⁻¹ᵁ (W i)).toScheme.ringCatSheaf)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pushforward f).obj L) ∧
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L) := by
  apply DescGlob.core
  intro x
  have hx : x ∈ (U ⊔ ⨆ i, W i : X.Opens) := by rw [hcov]; trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hx with hxU | hxW
  · haveI := hU
    exact DescGlob.exists_nhd_of_mem_isoLocus f U L hL hxU
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxW
    exact ⟨W i, hi, hO i, hW i⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app (solution)
