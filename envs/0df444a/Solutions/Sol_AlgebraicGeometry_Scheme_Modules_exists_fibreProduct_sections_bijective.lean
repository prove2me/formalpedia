-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_fibreProduct_sections_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/51028b33-1727-5bd4-a5ba-2c042db6f9f1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Γ Modules Opens evaluation"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf pullback presheaf"
namespace FibreProductSections
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

noncomputable def evalForget (U : X.Opens) : TopCat.Presheaf Ab X ⥤ Type u :=
  (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget Ab

noncomputable scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (evalForget (X := X) U) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U) ⋙ CategoryTheory.forget Ab.{u}))

noncomputable def sectionsFunctorAt (U : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ evalForget U

noncomputable scoped instance (U : X.Opens) :
    PreservesLimitsOfShape WalkingCospan (sectionsFunctorAt (X := X) U) := by
  unfold sectionsFunctorAt; infer_instance

theorem sectionsFunctorAt_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    (sectionsFunctorAt U).map φ x = φ.app U x := rfl

end AlgebraicGeometry.Scheme.Modules.FibreProductSections
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules.FibreProductSections"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry"

open CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FibreProductSections in

theorem solution
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by
  have key : ∀ U : X.Opens, ∃ e : (Γ(Limits.pullback a b, U) : Type u) ≃
      Types.PullbackObj ((sectionsFunctorAt U).map a) ((sectionsFunctorAt U).map b),
      ∀ s, (e s).1.1 = (pullback.fst a b).app U s ∧ (e s).1.2 = (pullback.snd a b).app U s := by
    intro U
    have hc := isLimitPullbackConeMapOfIsLimit (sectionsFunctorAt U) pullback.condition
      (pullbackIsPullback a b)
    exact ⟨PullbackCone.IsLimit.equivPullbackObj hc, fun s =>
      ⟨PullbackCone.IsLimit.equivPullbackObj_apply_fst hc s,
       PullbackCone.IsLimit.equivPullbackObj_apply_snd hc s⟩⟩
  refine ⟨Limits.pullback a b, pullback.fst a b, pullback.snd a b, pullback.condition, ?_, ?_⟩
  · intro U s t hst
    obtain ⟨e, he⟩ := key U
    apply e.injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [(he s).1, (he t).1]; exact congrArg Prod.fst hst
    · rw [(he s).2, (he t).2]; exact congrArg Prod.snd hst
  · intro U s₀ s₁ h
    obtain ⟨e, he⟩ := key U
    refine ⟨e.symm ⟨(s₀, s₁), h⟩, ?_, ?_⟩
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).2
      rw [Equiv.apply_symm_apply] at this
      exact this.symm

end S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective (solution)
