-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/838c31e7-2f8a-5c66-9163-a3677363834b

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.AlgebraicGeometry"
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.baseChangeHom Scheme.Modules.unit_app_comp_pullbackComp_inv"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.pushforward Modules.pullback Hom Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens Modules.pullbackComp Modules.baseChangeHom Modules.unit_app_comp_pullbackComp_inv"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforward pullback presheaf Hom.comp_app Hom Hom.app pullbackPushforwardAdjunction pullbackComp baseChangeHom unit_app_app_comp_baseChangeHom_app unit_app_comp_pullbackComp_inv"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem phE5_map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U V : Y.Opens}
    (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U = φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

theorem phE5_map_eqToHom_comp_map_eqToHom {Y : Scheme.{u}} (M : Y.Modules) {A₁ A₂ B₁ : Y.Opens}
    (a : A₁ = A₂) (b : B₁ = A₁) :
    M.presheaf.map (eqToHom a).op ≫ M.presheaf.map (eqToHom b).op =
      M.presheaf.map (eqToHom (b.trans a)).op := by
  subst a; subst b; simp

theorem phE5_ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T) {M : T.Modules} {N : T'.Modules}
    (f₁ f₂ : (pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens, ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₁.app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫ f₂.app (ψ ⁻¹ᵁ U)) : f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  exact h U

theorem phE5_inv_app_map_eqToHom_hom_app {Y : Scheme.{u}} {P Q : Y.Modules} (c : P ≅ Q) {W₁ W₃ : Y.Opens}
    (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ c.hom.app W₃ = Q.presheaf.map (eqToHom e).op := by
  subst e
  simp [← Scheme.Modules.Hom.comp_app]

set_option maxHeartbeats 1600000 in
theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.solution
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''} {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ))
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂ ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map ((Scheme.Modules.pullbackComp g'' g').hom.app F) := by
  apply phE5_ext_of_unit_app_comp (ψ' ≫ ψ)
  intro U
  have e₁ : (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π'' ≫ ψ') ⁻¹ᵁ (ψ ⁻¹ᵁ U) = (g'' ≫ π') ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by rw [h₂]
  have e₁g : g'' ⁻¹ᵁ ((π' ≫ ψ) ⁻¹ᵁ U) = g'' ⁻¹ᵁ ((g' ≫ π) ⁻¹ᵁ U) := by rw [h₁]

  rw [unit_app_app_comp_baseChangeHom_app π (ψ' ≫ ψ) π'' (g'' ≫ g') h₁₂ F U]

  have s0 : ((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U ≫ ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ ((pullbackPushforwardAdjunction ψ').unit.app ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv ψ' ψ ((pushforward π).obj F) U
  show _ = (((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app ((pushforward π).obj F)).app U ≫ ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫ ((pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s0]

  have s1 : ((pullbackPushforwardAdjunction ψ').unit.app ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) = (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) := by
    have n := congrArg (fun t => Scheme.Modules.Hom.app t (ψ ⁻¹ᵁ U))
      ((pullbackPushforwardAdjunction ψ').unit.naturality (baseChangeHom h₁ F))
    simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app] at n
    exact n.symm
  show _ = ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (((pullbackPushforwardAdjunction ψ').unit.app ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) ≫ ((pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫ (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s1]

  have t1 : ((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullback g').obj F).presheaf.map (eqToHom e₁).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π' g' h₁ F U
  show _ = (((pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F)).app U ≫ (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U)) ≫ ((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t1]

  have t2 : ((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) = ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π' ψ' π'' g'' h₂ ((pullback g').obj F) (ψ ⁻¹ᵁ U)
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫ (((pullbackPushforwardAdjunction ψ').unit.app ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫ (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t2]

  have u4 : ((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫ ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₁g).op :=
    phE5_map_eqToHom_comp_app ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)) e₁
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ (((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫ ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₂).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [u4]

  have s3 : ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) = ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) :=
    Scheme.Modules.unit_app_comp_pullbackComp_inv g'' g' F (π ⁻¹ᵁ U)
  show _ = (((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U))) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₁g).op ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₂).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [← s3]

  have m : ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₁g).op ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₂).op = ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom (e₂.trans e₁g)).op :=
    phE5_map_eqToHom_comp_map_eqToHom ((pullback g'').obj ((pullback g').obj F)) e₁g e₂
  show _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫ ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ (((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₁g).op ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom e₂).op) ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [m]

  have fin : ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom (e₂.trans e₁g)).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)) = ((pullback (g'' ≫ g')).obj F).presheaf.map (eqToHom (e₂.trans e₁g)).op :=
    phE5_inv_app_map_eqToHom_hom_app ((pullbackComp g'' g').app F) (e₂.trans e₁g)
  show _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app (π ⁻¹ᵁ U) ≫ (((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫ ((pullback g'').obj ((pullback g').obj F)).presheaf.map (eqToHom (e₂.trans e₁g)).op ≫ ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)))
  erw [fin]
  rfl

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal (solution)
