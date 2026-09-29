-- Prove2me | solution 1 for AlgebraicGeometry.forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d0fa029a-58f0-5899-a2e7-ee5056c6b305

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
import Theorems.Thm_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R₀ L : Type} [CommRing R₀] [CommRing L] (φ : R₀ →+* L) (hφ : Function.Injective φ)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (hs : Smooth f₀) (hp : IsProper f₀)
    (hconn : ∀ t : ↥(Spec (CommRingCat.of R₀)), _root_.IsConnected (f₀.base ⁻¹' {t}))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of L)) (g : A ⟶ A₀)
    (hg : IsPullback g f f₀ (Spec.map (CommRingCat.ofHom φ)))
    (d : ℕ) (hdim : ∀ x : ↥(Spec (CommRingCat.of L)), topologicalKrullDim ↥(f.base ⁻¹' {x}) = d)
    (t : ↥(Spec (CommRingCat.of R₀))) : topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d := by
  have hW : IsClopen {t : ↥(Spec (CommRingCat.of R₀)) | topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d} :=
    AlgebraicGeometry.isClopen_setOf_topologicalKrullDim_preimage_eq_of_smooth_of_isProper f₀ hs hp d
  have hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆
      {t : ↥(Spec (CommRingCat.of R₀)) | topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d} := by
    rintro _ ⟨x, rfl⟩
    show topologicalKrullDim ↥(f₀.base ⁻¹' {(Spec.map (CommRingCat.ofHom φ)).base x}) = d
    rw [← AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected f₀ hs
      (Spec.map (CommRingCat.ofHom φ)) f g hg x (hconn _)]
    exact hdim x
  have := AlgebraicGeometry.eq_univ_of_isClopen_of_range_specMap_subset_of_injective φ hφ _ hW hWL
  have ht : t ∈ {t : ↥(Spec (CommRingCat.of R₀)) | topologicalKrullDim ↥(f₀.base ⁻¹' {t}) = d} := by rw [this]; trivial
  exact ht

end S_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected
end P2MW
export P2MW.S_AlgebraicGeometry_forall_topologicalKrullDim_preimage_eq_of_isPullback_of_injective_of_isConnected (solution)
