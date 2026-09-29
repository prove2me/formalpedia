-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f8ce0ebe-b09b-5013-a93a-49405507e19f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} (W : X.Opens) (hW : IsAffineOpen W) (O : X.Opens) (F : Finset X)
    (hFW : ∀ x ∈ F, x ∈ W) (hFO : ∀ x ∈ F, x ∈ O) :
    ∃ W' : X.Opens, IsAffineOpen W' ∧ W' ≤ W ⊓ O ∧ ∀ x ∈ F, x ∈ W' := by
  classical

  have stepA : ∀ (R : Type u) [CommRing R] (O' : TopologicalSpace.Opens (PrimeSpectrum R))
      (F' : Finset (PrimeSpectrum R)), (∀ p ∈ F', p ∈ O') →
      ∃ a : R, PrimeSpectrum.basicOpen a ≤ O' ∧ ∀ p ∈ F', p ∈ PrimeSpectrum.basicOpen a := by
    intro R _ O' F' hF'
    set Z : Set (PrimeSpectrum R) := (O' : Set (PrimeSpectrum R))ᶜ with hZ
    have hZc : IsClosed Z := O'.isOpen.isClosed_compl
    set I : Ideal R := PrimeSpectrum.vanishingIdeal Z with hI
    have hZI : PrimeSpectrum.zeroLocus (I : Set R) = Z := by
      rw [hI, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
    rcases F'.eq_empty_or_nonempty with hF0 | ⟨p₀, hp₀⟩
    · refine ⟨0, ?_, by simp [hF0]⟩
      rw [PrimeSpectrum.basicOpen_zero]; exact bot_le
    have hnot : ¬ ((I : Set R) ⊆ ⋃ p ∈ F', ((fun q : PrimeSpectrum R => q.asIdeal) p : Set R)) := by
      intro hsub
      obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime p₀ p₀
        (fun (q : PrimeSpectrum R) _ _ _ => q.isPrime) (s := F') (f := fun q : PrimeSpectrum R => q.asIdeal)
        (I := I)).mp hsub
      have : p ∈ Z := by
        rw [← hZI]; exact hle
      exact this (hF' p hp)
    rw [Set.not_subset] at hnot
    obtain ⟨a, haI, ha⟩ := hnot
    simp only [Set.mem_iUnion, not_exists] at ha
    refine ⟨a, fun y hy => ?_, fun p hp => ha p hp⟩
    by_contra hyO
    have hyZ : y ∈ Z := hyO
    rw [← hZI] at hyZ
    exact hy (hyZ haI)

  have hsurj : ∀ x ∈ F, ∃ p : Spec Γ(X, W), hW.fromSpec p = x := fun x hx => by
    have : x ∈ Set.range ⇑hW.fromSpec := by rw [hW.range_fromSpec]; exact hFW x hx
    exact this
  choose p hp using hsurj
  let F' : Finset (PrimeSpectrum Γ(X, W)) := F.attach.image fun x => p x.1 x.2
  obtain ⟨a, haO, haF⟩ := stepA Γ(X, W) (hW.fromSpec ⁻¹ᵁ O) F' (by
    intro q hq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
    change hW.fromSpec (p x.1 x.2) ∈ O
    rw [hp]; exact hFO x.1 x.2)
  refine ⟨X.basicOpen a, hW.basicOpen a, ?_, ?_⟩
  · intro y hy
    refine ⟨X.basicOpen_le a hy, ?_⟩
    have hyW : y ∈ Set.range ⇑hW.fromSpec := by rw [hW.range_fromSpec]; exact X.basicOpen_le a hy
    obtain ⟨q, rfl⟩ := hyW
    have hq : q ∈ PrimeSpectrum.basicOpen a := by
      rw [← hW.fromSpec_preimage_basicOpen a]; exact hy
    exact haO hq
  · intro x hx
    have hq : p x hx ∈ PrimeSpectrum.basicOpen a :=
      haF _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
    rw [← hW.fromSpec_preimage_basicOpen a] at hq
    change hW.fromSpec (p x hx) ∈ X.basicOpen a at hq
    rwa [hp] at hq

end S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset (solution)
