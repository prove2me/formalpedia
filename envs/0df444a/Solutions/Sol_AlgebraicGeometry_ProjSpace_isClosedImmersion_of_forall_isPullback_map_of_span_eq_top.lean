-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d4294b0f-156a-5f19-80eb-366c96530d21

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    (N : ℕ) {X : Scheme.{u}} (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S))
    {X' : Fin k → Scheme.{u}} (t' : ∀ i, X' i ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (B i)))
    (g : ∀ i, X' i ⟶ X) (hsq : ∀ i, IsPullback (g i) (t' i) t (ProjSpace.map S (B i) N))
    (h : ∀ i, IsClosedImmersion (t' i)) :
    IsClosedImmersion t := by
  classical

  have hpb : ∀ i, IsPullback (ProjSpace.map S (B i) N) (ProjSpace.π (B i) N) (ProjSpace.π S N)
      (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) := fun i => AlgebraicGeometry.ProjSpace.isPullback_map S (B i) N
  have hopen : ∀ i, IsOpenImmersion (ProjSpace.map S (B i) N) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb i).flip (IsOpenImmersion.of_isLocalization (r i))

  have hcov : ∀ x : ↥(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      ∃ (i : Fin k) (y : ↥(Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (B i)))),
        (ProjSpace.map S (B i) N).base y = x := by
    intro x
    set s := (ProjSpace.π S N).base x with hs
    have hx : ¬ (Set.range r ⊆ (s.asIdeal : Set S)) := by
      intro hsub
      have : (⊤ : Ideal S) ≤ s.asIdeal := hr ▸ Ideal.span_le.mpr hsub
      exact s.isPrime.ne_top (top_le_iff.mp this)
    obtain ⟨_, ⟨i, rfl⟩, hri⟩ := Set.not_subset.mp hx
    have hmem : s ∈ (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum S)) := hri
    rw [← PrimeSpectrum.localization_away_comap_range (B i) (r i)] at hmem
    obtain ⟨s', hs'⟩ := hmem
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ProjSpace.π S N)
      (g := Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) x s' (by rw [← hs]; exact hs'.symm)
    refine ⟨i, ((hpb i).isoPullback).inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, (hpb i).isoPullback_inv_fst]
    exact hz1
  let 𝒰 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)).OpenCover :=
    Scheme.Cover.mkOfCovers (Fin k) (fun i => Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (B i)))
      (fun i => ProjSpace.map S (B i) N) hcov
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰 fun i => ?_
  show IsClosedImmersion (pullback.snd t (ProjSpace.map S (B i) N))
  rw [← (hsq i).isoPullback_inv_snd]
  infer_instance

end S_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top (solution)
