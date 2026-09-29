-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.eq_of_preimage_basicOpen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/95c8c09a-20d1-57eb-bc07-05f004d7b9e8

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

namespace F2USol

open AlgebraicGeometry.GradedOAlgebra

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (θ₁ θ₂ : X ⟶ Proj 𝓡)
    (h₁ : IsCanonicalToProj f L R 𝓡 ι θ₁) (h₂ : IsCanonicalToProj f L R 𝓡 ι θ₂)
    (hpre : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
    (hpow : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ),
      Scheme.Modules.IsFrameOn (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)))

include h₂ in

theorem appLE_smul_of_eq (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (k : ℕ) (s : 𝓡 (k • n))
    (W : X.Opens) (hW : W = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) :
    (θ₂.appLE (Proj.basicOpen 𝓡 (σ : R)) W hW.le
        (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k (s : R) s.2))) •
      (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩)
    = (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (k • n) s) := by
  subst hW
  exact h₂.appLE_awayToSection_smul n hn σ k s

include h₁ h₂ hpre hpow in

theorem appLE_eq (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) :
    θ₁.appLE (Proj.basicOpen 𝓡 (σ : R)) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl =
      θ₂.appLE (Proj.basicOpen 𝓡 (σ : R)) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) (hpre n hn σ).le := by
  ext x
  have hsurj : Function.Surjective (Proj.awayToSection 𝓡 (σ : R)) := by
    rw [← Proj.basicOpenIsoAway_hom 𝓡 (σ : R) σ.2 hn]
    exact (ConcreteCategory.bijective_of_isIso _).2
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝓡 σ.2 y
  have e₁ := h₁.appLE_awayToSection_smul n hn σ k ⟨a, ha⟩
  have e₂ := appLE_smul_of_eq f L R 𝓡 ι θ₂ h₂ n hn σ k ⟨a, ha⟩ (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) (hpre n hn σ)
  exact ((hpow n hn σ k).existsUnique le_top le_rfl _).unique e₁ e₂

include h₁ h₂ hpre hpow in

theorem resLE_eq (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) :
    θ₁.resLE (Proj.basicOpen 𝓡 (σ : R)) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl =
      θ₂.resLE (Proj.basicOpen 𝓡 (σ : R)) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) (by rw [hpre n hn σ]) := by
  haveI : IsAffine (Proj.basicOpen 𝓡 (σ : R)).toScheme := Proj.isAffineOpen_basicOpen 𝓡 (σ : R) σ.2 hn
  apply ext_of_isAffine
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_eq f L R 𝓡 ι θ₁ θ₂ h₁ h₂ hpre hpow n hn σ]

end F2USol

open F2USol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
    (θ₁ θ₂ : X ⟶ Proj 𝓡)
    (h₁ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₁)
    (h₂ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₂)
    (hpre : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
    (hpow : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ),
      Scheme.Modules.IsFrameOn (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    θ₁ = θ₂ := by
  refine Scheme.hom_ext_of_forall θ₁ θ₂ fun x => ?_
  obtain ⟨i, y, hy⟩ := (Proj.affineOpenCover 𝓡).openCover.exists_eq (θ₁.base x)
  have hx : θ₁.base x ∈ Proj.basicOpen 𝓡 (i.2 : R) := by
    rw [← Proj.opensRange_awayι 𝓡 (i.2 : R) i.2.2 i.1.2]; exact ⟨y, hy⟩
  refine ⟨θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (i.2 : R), hx, ?_⟩
  have key := resLE_eq f L R 𝓡 ι θ₁ θ₂ h₁ h₂ hpre hpow i.1.1 i.1.2 i.2
  have e₁ := Scheme.Hom.resLE_comp_ι θ₁ (U := Proj.basicOpen 𝓡 (i.2 : R)) (V := θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (i.2 : R)) le_rfl
  have e₂ := Scheme.Hom.resLE_comp_ι θ₂ (U := Proj.basicOpen 𝓡 (i.2 : R)) (V := θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (i.2 : R))
    (by rw [hpre i.1.1 i.1.2 i.2])
  rw [← e₁, ← e₂, key]

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq (solution)
