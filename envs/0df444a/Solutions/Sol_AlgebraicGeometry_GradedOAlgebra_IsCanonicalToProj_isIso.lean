-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/29770565-7a86-5943-9ad0-6dc1738183f5

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso_morphismRestrict_basicOpen_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_denseRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) : IsIso θ := by
  classical
  obtain ⟨N, 𝔓, h𝔓⟩ := hva

  have hτ : ∀ i : Fin (N + 1), ∃ τ : 𝓡 1, (λ_ L).hom.app ⊤ (ι 1 τ) = 𝔓.σ i := by
    intro i
    obtain ⟨τ, hτ⟩ := (hR.bijective 1).2 ((λ_ L).inv.app ⊤ (𝔓.σ i))
    refine ⟨τ, ?_⟩
    rw [hτ]
    change ((λ_ L).inv ≫ (λ_ L).hom).app ⊤ (𝔓.σ i) = 𝔓.σ i
    rw [Iso.inv_hom_id]
    rfl
  choose τ hτ using hτ
  have hchart := fun i =>
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
      f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ N 𝔓 h𝔓 i (τ i) (hτ i)

  let U : Fin (N + 1) → (Proj 𝓡).Opens := fun i => Proj.basicOpen 𝓡 ((τ i : 𝓡 1) : R)

  have hiso : ∀ i, IsIso (θ ∣_ U i) := fun i =>
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso_morphismRestrict_basicOpen_of_isAffineOpen
      f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ 1 one_pos (τ i) (hchart i).2

  have hpre : θ ⁻¹ᵁ (⨆ i, U i) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    have h1 : (⨆ i, θ ⁻¹ᵁ U i) = ⨆ i, 𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) :=
      iSup_congr fun i => (hchart i).1
    rw [h1, ← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X S N),
      Scheme.Hom.preimage_top]

  have hsurj : Function.Surjective θ.base := by
    haveI := AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.universallyClosed f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ
    have hcl : IsClosed (Set.range θ.base) := θ.isClosedMap.isClosed_range
    have hd := AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.denseRange f L R 𝓡 ι hR hL ⟨N, 𝔓, h𝔓⟩ θ hθ
    rw [← Set.range_eq_univ, ← hcl.closure_eq, hd.closure_range]

  have hU : (⨆ i, U i) = ⊤ := by
    refine le_antisymm le_top fun p _ => ?_
    obtain ⟨x, rfl⟩ := hsurj p
    have hx : x ∈ θ ⁻¹ᵁ (⨆ i, U i) := by rw [hpre]; trivial
    exact hx

  have key : (MorphismProperty.isomorphisms Scheme) θ :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU
      fun i => (MorphismProperty.isomorphisms.iff _).mpr (hiso i)
  exact (MorphismProperty.isomorphisms.iff _).mp key

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_isIso (solution)
