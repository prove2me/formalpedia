-- Prove2me | solution 1 for AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6a19b4a3-7fbb-5273-baa9-27f6ca9d5bc1

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.AlgebraicGeometry Opposite TensorProduct"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.pushforward tilde.adjunction moduleSpecΓFunctor Spec Spec.map Scheme pullbackSpecIso Scheme.Modules.pullbackPushforwardAdjunction tilde.functor Scheme.Modules tilde tilde.toOpen Scheme.Modules.pushforwardSpecCompΓIso tilde.pullbackSpecIso" namespace tilde p2m_export "AlgebraicGeometry.tilde" "adjunction toOpen pullbackSpecIso" end AlgebraicGeometry.tilde
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.tilde" in

theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
  exact h2

theorem solution {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by
  have h := congrArg (fun ψ => ψ.hom m) (AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux φ M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Adjunction.comp_unit_app, Functor.comp_map] at h
  exact h

#print axioms solution

end S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
end P2MW
export P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen (solution)
