-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/949006ba-f71f-5d33-aaef-08d5b5b9f56f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules Scheme.Modules.baseChangeHom Scheme.Modules.unit_app_comp_pullbackComp_inv"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Hom mk Modules.Hom.comp_app Modules.Hom Hom.comp_app Modules Opens Modules.baseChangeHom Modules.unit_app_comp_pullbackComp_inv"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforwardCongr pushforward pushforwardComp pullback presheaf Hom.comp_app pushforwardId Hom pullbackPushforwardAdjunction pullbackComp baseChangeHom unit_app_app_comp_baseChangeHom_app unit_app_comp_pullbackComp_inv"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem invE5_map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens}
    (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U = φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

theorem invE5_inv_app_map_eqToHom_id_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁ W₃ : Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ 𝟙 _ ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom e).op := by
  subst e
  simp [← Scheme.Modules.Hom.comp_app]

theorem invE5_ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) {M : T.Modules} {N : T'.Modules}
    (f₁ f₂ : (pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens, ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₁.app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₂.app (ψ ⁻¹ᵁ U)) : f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact h U

noncomputable def invE5_pushforwardIsoEquivalence {Y Y' : Scheme.{u}} (e : Y ≅ Y') : Y.Modules ≌ Y'.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    ((pushforwardId Y).symm ≪≫ pushforwardCongr e.hom_inv_id.symm ≪≫ (pushforwardComp e.hom e.inv).symm)
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Y')

set_option maxHeartbeats 1600000 in

theorem invE5_baseChangeHom_iso_comp {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X} (θ : X₁ ≅ X₂) (h₂ : g₂ ≫ π = π₂ ≫ ψ)
    (h₁ : (θ.hom ≫ g₂) ≫ π = (θ.hom ≫ π₂) ≫ ψ) (F : X.Modules) :
    baseChangeHom h₁ F =
      baseChangeHom h₂ F ≫ (pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((pullback θ.hom).obj ((pullback g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F) := by
  apply invE5_ext_of_unit_app_comp ψ
  intro U
  have e₁ : ((θ.hom ≫ π₂) ≫ ψ) ⁻¹ᵁ U = ((θ.hom ≫ g₂) ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π₂ ≫ ψ) ⁻¹ᵁ U = (g₂ ≫ π) ⁻¹ᵁ U := by rw [h₂]
  have e₂θ : θ.hom ⁻¹ᵁ ((π₂ ≫ ψ) ⁻¹ᵁ U) = θ.hom ⁻¹ᵁ ((g₂ ≫ π) ⁻¹ᵁ U) := by rw [h₂]

  rw [unit_app_app_comp_baseChangeHom_app π ψ (θ.hom ≫ π₂) (θ.hom ≫ g₂) h₁ F U]

  show _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))

  have t2 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullback g₂).obj F).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π₂ g₂ h₂ F U
  show _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (baseChangeHom h₂ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [t2]

  have u : ((pullback g₂).obj F).presheaf.map (eqToHom e₂).op ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback θ.hom).obj ((pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op :=
    invE5_map_eqToHom_comp_app ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)) e₂
  show _ = ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ (((pullback g₂).obj F).presheaf.map (eqToHom e₂).op ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (π₂ ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [u]

  have s3 : ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv θ.hom g₂ F (π ⁻¹ᵁ U)
  show _ = (((pullbackPushforwardAdjunction g₂).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)).app (g₂ ⁻¹ᵁ (π ⁻¹ᵁ U))) ≫ ((pullback θ.hom).obj ((pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U))
  erw [← s3]

  have fin : ((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback θ.hom).obj ((pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)) = ((pullback (θ.hom ≫ g₂)).obj F).presheaf.map (eqToHom e₂θ).op :=
    invE5_inv_app_map_eqToHom_id_hom_app ((pullbackComp θ.hom g₂).app F) e₂θ
  show _ = ((pullbackPushforwardAdjunction (θ.hom ≫ g₂)).unit.app F).app (π ⁻¹ᵁ U) ≫ (((pullbackComp θ.hom g₂).inv.app F).app ((θ.hom ≫ g₂) ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback θ.hom).obj ((pullback g₂).obj F)).presheaf.map (eqToHom e₂θ).op ≫ 𝟙 _ ≫ ((pullbackComp θ.hom g₂).hom.app F).app ((θ.hom ≫ π₂) ⁻¹ᵁ (ψ ⁻¹ᵁ U)))
  erw [fin]
  rfl

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback.solution
    {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₁ : X₁ ⟶ T'} {g₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X}
    (h₁ : IsPullback g₁ π₁ π ψ) (h₂ : IsPullback g₂ π₂ π ψ) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom h₁.w F) ↔ IsIso (Scheme.Modules.baseChangeHom h₂.w F) := by
  obtain ⟨θ, hθg, hθπ⟩ : ∃ θ : X₁ ≅ X₂, θ.hom ≫ g₂ = g₁ ∧ θ.hom ≫ π₂ = π₁ :=
    ⟨h₁.isoIsPullback _ _ h₂, IsPullback.isoIsPullback_hom_fst _ _ h₁ h₂, IsPullback.isoIsPullback_hom_snd _ _ h₁ h₂⟩
  subst hθg
  subst hθπ
  rw [invE5_baseChangeHom_iso_comp θ h₂.w h₁.w F]

  haveI : (pushforward θ.hom).IsEquivalence := (invE5_pushforwardIsoEquivalence θ).isEquivalence_functor
  haveI i0 : IsIso ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)) := inferInstance
  haveI i1 : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F))) :=
    Functor.map_isIso _ _
  haveI i2 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((pullback θ.hom).obj ((pullback g₂).obj F))) :=
    inferInstance
  haveI i3 : IsIso ((pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    Functor.map_isIso _ _
  haveI i23 : IsIso ((pushforwardComp θ.hom π₂).hom.app ((pullback θ.hom).obj ((pullback g₂).obj F)) ≫
      (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i2 i3
  haveI iW : IsIso ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)) ≫
      (pushforwardComp θ.hom π₂).hom.app ((pullback θ.hom).obj ((pullback g₂).obj F)) ≫
        (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i23
  constructor
  · intro h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (baseChangeHom h₂.w F)
      ((pushforward π₂).map ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback g₂).obj F)) ≫
        (pushforwardComp θ.hom π₂).hom.app ((pullback θ.hom).obj ((pullback g₂).obj F)) ≫
          (pushforward (θ.hom ≫ π₂)).map ((pullbackComp θ.hom g₂).hom.app F)) iW h
  · intro h
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h iW

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback (solution)
