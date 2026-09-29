-- Prove2me | solution 1 for AlgebraicGeometry.exists_iso_Spec_of_isClopen_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9db7c604-6453-5405-82ff-3c177bf3884d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {K : Scheme.{u}} (p : K ⟶ Spec (CommRingCat.of S)) [IsFinite p] [Flat p]
    (𝒢 : K.Opens) (h𝒢 : IsClosed (𝒢 : Set ↥K)) :
    ∃ (S' : Type u) (_ : CommRing S') (φ : S →+* S') (e : Spec (CommRingCat.of S') ≅ (𝒢 : Scheme.{u})),
      e.hom ≫ 𝒢.ι ≫ p = Spec.map (CommRingCat.ofHom φ) ∧
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      (Surjective (𝒢.ι ≫ p) → Surjective (Spec.map (CommRingCat.ofHom φ))) := by
  classical
  haveI : IsAffineHom p := inferInstance
  haveI : IsAffine K := isAffine_of_isAffineHom p

  haveI : IsClosedImmersion 𝒢.ι := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [Scheme.Opens.range_ι]; exact h𝒢
  haveI : IsAffine (𝒢 : Scheme.{u}) := isAffine_of_isAffineHom 𝒢.ι
  let G : Scheme.{u} := 𝒢
  let e : Spec Γ(G, ⊤) ≅ G := G.isoSpec.symm
  let f : Spec Γ(G, ⊤) ⟶ Spec (CommRingCat.of S) := e.hom ≫ 𝒢.ι ≫ p
  let φ : S →+* Γ(G, ⊤) := (Spec.preimage f).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = f := by
    simp only [φ, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨Γ(G, ⊤), inferInstance, φ, e, hφ.symm, ?_, ?_⟩
  · rw [hφ]; infer_instance
  · intro hs; rw [hφ]; haveI := hs; infer_instance

end S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat (solution)
