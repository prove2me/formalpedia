-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f89d21a5-a25e-5249-8385-f46f8bbe5a5d

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X P X₀ : Scheme.{u}} (p : P ⟶ X) (e : X₀ ≅ P) (g : X₀ ⟶ X) (hge : e.hom ≫ p = g) (M : X.Modules)
    (h : ∀ y : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ ⊤),
      ∃ σ : Γ(M, ⊤), Scheme.Modules.pullbackLocalSection p σ = y)
    (s₀ : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤)) :
    ∃ σ : Γ(M, ⊤), Scheme.Modules.pullbackLocalSection g σ = s₀ := by
  subst hge

  have e' : (Scheme.Modules.pullback p).obj M ≅
      (Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pushforward e.inv).obj ((Scheme.Modules.pullback p).obj M)) :=
    ((Scheme.Modules.pushforwardId P).app _).symm ≪≫ ((Scheme.Modules.pushforwardCongr e.inv_hom_id).app _).symm ≪≫
      ((Scheme.Modules.pushforwardComp e.inv e.hom).app _).symm
  haveI hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app ((Scheme.Modules.pullback p).obj M)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom).isIso_unit_app_of_iso e'

  let y' : Γ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback p).obj M), e.hom ⁻¹ᵁ (p ⁻¹ᵁ ⊤)) :=
    ((Scheme.Modules.pullbackComp e.hom p).inv.app M).app (e.hom ⁻¹ᵁ (p ⁻¹ᵁ ⊤)) s₀
  let y : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ ⊤) :=
    (inv ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app ((Scheme.Modules.pullback p).obj M))).app
      (p ⁻¹ᵁ ⊤) y'
  obtain ⟨σ, hσ⟩ := h y
  refine ⟨σ, ?_⟩
  have hy : Scheme.Modules.pullbackLocalSection e.hom y = y' := by
    rw [Scheme.Modules.pullbackLocalSection_def]
    change (inv ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app ((Scheme.Modules.pullback p).obj M)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app ((Scheme.Modules.pullback p).obj M)).app
        (p ⁻¹ᵁ ⊤) y' = y'
    rw [IsIso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  rw [← Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection e.hom p M ⊤ σ, hσ, hy]
  change ((Scheme.Modules.pullbackComp e.hom p).inv.app M ≫ (Scheme.Modules.pullbackComp e.hom p).hom.app M).app
      (e.hom ⁻¹ᵁ (p ⁻¹ᵁ ⊤)) s₀ = s₀
  rw [Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_pullbackLocalSection_eq_of_iso_hom_comp_eq (solution)
