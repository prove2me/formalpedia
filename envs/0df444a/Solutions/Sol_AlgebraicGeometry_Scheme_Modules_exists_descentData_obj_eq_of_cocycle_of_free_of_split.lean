-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a56e3c5c-1b8c-58d3-8e4a-e00ce84c12d1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hfree : ∀ ⦃Z : Scheme.{u}⦄ (v : Z ⟶ X) (g : G), Nonempty ↥Z → v ≫ σ g = v → g = 0)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψ0 : ψ 0 = ((Scheme.Modules.pullbackId X).app M).symm ≪≫ ((Scheme.Modules.pullbackCongr hσ0).app M).symm)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => q),
      ∀ i, D.obj i = M := by

  let a₁ := pullback.fst q q
  let a₂ := pullback.snd q q
  have ha : a₁ ≫ q = a₂ ≫ q := pullback.condition
  let b₁₂ := pullback.fst a₂ a₁
  let b₂₃ := pullback.snd a₂ a₁
  have h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁ := pullback.condition
  let b₁₃ : pullback a₂ a₁ ⟶ pullback q q := pullback.lift (b₁₂ ≫ a₁) (b₂₃ ≫ a₂)
    (by rw [Category.assoc, ha, ← Category.assoc, h₂, Category.assoc, Category.assoc, ha])
  have h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁ := (pullback.lift_fst _ _ _).symm
  have h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂ := pullback.lift_snd _ _ _
  obtain ⟨Ψ, hΨ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_forall_mapIso_eq_of_free_of_split
    q G σ hσ0 hσadd hfree hsplit M ψ a₁ a₂ ha
  have hcoc := AlgebraicGeometry.Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
    q G σ hσadd hsplit M ψ hψadd a₁ a₂ ha b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ Ψ hΨ
  exact AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_isPullback
    q a₁ a₂ (IsPullback.of_hasPullback q q) b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ (IsPullback.of_hasPullback a₂ a₁) M Ψ hcoc

end S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split (solution)
