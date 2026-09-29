-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.congr_and_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f4e67476-7309-529b-8936-edca4d341ae2

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace BenchR_EDb

universe u

theorem specMap_ofHom_id (S : Type u) [CommRing S] :
    Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

end BenchR_EDb

open BenchR_EDb in
theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] :
    (∀ (φ ψ : S →+* S') (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S'),
      φ = ψ → PolarisedAbelianScheme.IsPullback φ u v → PolarisedAbelianScheme.IsPullback ψ u v) ∧
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.IsPullback (RingHom.id S) u u) := by
  refine ⟨?_, ?_⟩
  · rintro φ ψ u v rfl h
    exact h
  · intro u
    have e : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 (Spec (CommRingCat.of S)) :=
      specMap_ofHom_id S
    haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by rw [e]; infer_instance
    have hg : CategoryTheory.IsPullback (𝟙 u.A) u.f u.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by rw [e]; simp⟩
    refine ⟨𝟙 u.A, hg, ?_, ?_, ?_⟩
    · intro T t' x y
      have hψ : 𝟙 T ≫ t' = t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by rw [e]; simp
      have key := u.L.mul_natural t' (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S))) (𝟙 T) hψ x y
      have hx : schemeHomOverComp (𝟙 T) hψ x =
          ⟨x.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩ :=
        Subtype.ext (by simp [schemeHomOverComp])
      have hy : schemeHomOverComp (𝟙 T) hψ y =
          ⟨y.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩ :=
        Subtype.ext (by simp [schemeHomOverComp])
      rw [← hx, ← hy, ← key]
      simp [schemeHomOverComp]
    · intro i
      rw [e]; simp
    · exact ⟨(Scheme.Modules.pullbackId u.A).app u.pol⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_congr_and_id (solution)
