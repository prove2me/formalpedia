-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_vertical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e36f9935-6170-562d-891d-cd18f66ffd7d

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.pushforward Scheme.Modules.pushforwardComp Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.baseChangeHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.pushforward Modules.pushforwardComp Modules.pullback Hom Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens Modules.baseChangeHom"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforward pushforwardComp pullback presheaf Hom.comp_app Hom pushforward_map_app Hom.app pullbackPushforwardAdjunction baseChangeHom unit_app_app_comp_baseChangeHom_app"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pvE5_map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens}
    (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U = φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

theorem pvE5_map_eqToHom_comp_map_eqToHom_comp_id {Y : Scheme.{u}} (M : Y.Modules) {A₁ A₂ B₁ : Y.Opens}
    (a : A₁ = A₂) (b : B₁ = A₁) :
    M.presheaf.map (eqToHom a).op ≫ M.presheaf.map (eqToHom b).op ≫ 𝟙 _ =
      M.presheaf.map (eqToHom (b.trans a)).op := by
  subst a; subst b; simp

theorem pvE5_ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) {M : T.Modules} {N : T'.Modules}
    (f₁ f₂ : (pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens, ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₁.app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₂.app (ψ ⁻¹ᵁ U)) : f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact h U

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical.solution
    {X Y T X' Y' T' : Scheme.{u}} {ρ : X ⟶ Y} {σ : Y ⟶ T} {ρ' : X' ⟶ Y'} {σ' : Y' ⟶ T'}
    {g' : X' ⟶ X} {k' : Y' ⟶ Y} {ψ : T' ⟶ T}
    (htop : g' ≫ ρ = ρ' ≫ k') (hbot : k' ≫ σ = σ' ≫ ψ) (h : g' ≫ (ρ ≫ σ) = (ρ' ≫ σ') ≫ ψ)
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h F =
      (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pushforwardComp ρ σ).inv.app F) ≫
        Scheme.Modules.baseChangeHom hbot ((Scheme.Modules.pushforward ρ).obj F) ≫
          (Scheme.Modules.pushforward σ').map (Scheme.Modules.baseChangeHom htop F) ≫
            (Scheme.Modules.pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F) := by
  apply pvE5_ext_of_unit_app_comp ψ
  intro U
  have eb : (σ' ≫ ψ) ⁻¹ᵁ U = (k' ≫ σ) ⁻¹ᵁ U := by rw [hbot]
  have eb' : ρ' ⁻¹ᵁ ((σ' ≫ ψ) ⁻¹ᵁ U) = ρ' ⁻¹ᵁ ((k' ≫ σ) ⁻¹ᵁ U) := by rw [hbot]
  have et : (ρ' ≫ k') ⁻¹ᵁ (σ ⁻¹ᵁ U) = (g' ≫ ρ) ⁻¹ᵁ (σ ⁻¹ᵁ U) := by rw [htop]

  rw [unit_app_app_comp_baseChangeHom_app (ρ ≫ σ) ψ (ρ' ≫ σ') g' h F U]

  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    pushforward_map_app]
  show _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫ ((pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)

  have s1 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫ ((pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app U := by
    have n := congrArg (fun t => Scheme.Modules.Hom.app t U)
      ((pullbackPushforwardAdjunction ψ).unit.naturality ((pushforwardComp ρ σ).inv.app F))
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj,
      Scheme.Modules.Hom.comp_app] at n
    have t : ((pushforwardComp ρ σ).inv.app F).app U ≫ ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app U = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫ ((pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U) := n
    have t2 : ((pushforwardComp ρ σ).inv.app F).app U = 𝟙 _ := rfl
    rw [t2] at t
    erw [Category.id_comp] at t
    exact t.symm
  show _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward (ρ ≫ σ)).obj F)).app U ≫ ((pullback ψ).map ((pushforwardComp ρ σ).inv.app F)).app (ψ ⁻¹ᵁ U)) ≫ (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  erw [s1]

  have tb : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app U ≫ (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫ ((pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op :=
    unit_app_app_comp_baseChangeHom_app σ ψ σ' k' hbot ((pushforward ρ).obj F) U
  show _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward σ).obj ((pushforward ρ).obj F))).app U ≫ (baseChangeHom hbot ((pushforward ρ).obj F)).app (ψ ⁻¹ᵁ U)) ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  erw [tb]

  have u3 : ((pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U) = (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U) ≫ ((pullback g').obj F).presheaf.map (eqToHom eb').op :=
    pvE5_map_eqToHom_comp_app (baseChangeHom htop F) eb
  show _ = ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫ (((pullback k').obj ((pushforward ρ).obj F)).presheaf.map (eqToHom eb).op ≫ (baseChangeHom htop F).app ((σ' ≫ ψ) ⁻¹ᵁ U)) ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  erw [u3]

  have tt : ((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫ (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g').unit.app F).app (ρ ⁻¹ᵁ (σ ⁻¹ᵁ U)) ≫ ((pullback g').obj F).presheaf.map (eqToHom et).op :=
    unit_app_app_comp_baseChangeHom_app ρ k' ρ' g' htop F (σ ⁻¹ᵁ U)
  show _ = (((pullbackPushforwardAdjunction k').unit.app ((pushforward ρ).obj F)).app (σ ⁻¹ᵁ U) ≫ (baseChangeHom htop F).app ((k' ≫ σ) ⁻¹ᵁ U)) ≫ ((pullback g').obj F).presheaf.map (eqToHom eb').op ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  erw [tt]

  have hpc : ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U) = 𝟙 _ := rfl
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app (ρ ⁻¹ᵁ (σ ⁻¹ᵁ U)) ≫ ((pullback g').obj F).presheaf.map (eqToHom et).op ≫ ((pullback g').obj F).presheaf.map (eqToHom eb').op ≫ ((pushforwardComp ρ' σ').hom.app ((pullback g').obj F)).app (ψ ⁻¹ᵁ U)
  erw [hpc]
  have m : ((pullback g').obj F).presheaf.map (eqToHom et).op ≫ ((pullback g').obj F).presheaf.map (eqToHom eb').op ≫ 𝟙 _ = ((pullback g').obj F).presheaf.map (eqToHom (eb'.trans et)).op :=
    pvE5_map_eqToHom_comp_map_eqToHom_comp_id ((pullback g').obj F) et eb'
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app (ρ ⁻¹ᵁ (σ ⁻¹ᵁ U)) ≫ (((pullback g').obj F).presheaf.map (eqToHom et).op ≫ ((pullback g').obj F).presheaf.map (eqToHom eb').op ≫ 𝟙 _)
  erw [m]
  rfl

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical (solution)
