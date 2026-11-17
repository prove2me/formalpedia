-- Prove2me | solution 1 for AlgebraicGeometry.Proj.exists_point_mem_ideal_iff_aeval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:43.825893+00:00
-- url     : https://prove2.me/submissions/419e709d-92f5-4def-99f4-c1f3b856876d

import Mathlib

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

namespace AlgebraicGeometry.Proj

/-- A nonzero tuple over an extension field determines a projective prime.
Homogeneous ideal containment is equivalent to vanishing on the tuple. -/
theorem _root_.solution
    {K L S : Type} [Field K] [Field L] [Algebra K L]
    (z : S → L) (hz : z ≠ 0) :
    ∃ x : ProjectiveSpectrum (homogeneousSubmodule S K),
      (∀ (p : MvPolynomial S K) (d : ℕ), p.IsHomogeneous d →
        (p ∈ x.asHomogeneousIdeal ↔ aeval z p = 0)) ∧
      (∀ I : HomogeneousIdeal (homogeneousSubmodule S K),
        I ≤ x.asHomogeneousIdeal ↔ ∀ p ∈ I.toIdeal, aeval z p = 0) := by
  classical
  let J : Ideal (MvPolynomial S K) := RingHom.ker (aeval z).toRingHom
  let H := J.homogeneousCore (homogeneousSubmodule S K)
  have hle : H.toIdeal ≤ J := Ideal.toIdeal_homogeneousCore_le _ _
  have hhom (p : MvPolynomial S K) (d : ℕ) (hp : p.IsHomogeneous d) :
      p ∈ H ↔ aeval z p = 0 := by
    constructor
    · intro h
      exact hle h
    · intro h
      exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hp⟩ h
  have hprime : H.toIdeal.IsPrime := by
    apply H.isHomogeneous.isPrime_of_homogeneous_mem_or_mem
    · intro heq
      have h : (1 : MvPolynomial S K) ∈ H.toIdeal := heq ▸ (show (1 : MvPolynomial S K) ∈ (⊤ : Ideal _) from trivial)
      have hzero : aeval z (1 : MvPolynomial S K) = 0 := hle h
      simpa using hzero
    · rintro p q ⟨d, hp⟩ ⟨e, hq⟩ hpq
      have hzero : aeval z (p * q) = 0 := hle hpq
      rw [map_mul, mul_eq_zero] at hzero
      exact hzero.elim (fun h => Or.inl ((hhom p d hp).mpr h))
        (fun h => Or.inr ((hhom q e hq).mpr h))
  have hrel : ¬HomogeneousIdeal.irrelevant (homogeneousSubmodule S K) ≤ H := by
    intro h
    apply hz
    funext i
    have hi : (X i : MvPolynomial S K) ∈ H :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (isHomogeneous_X K i))
    simpa using (hhom (X i) 1 (isHomogeneous_X K i)).mp hi
  refine ⟨⟨H, hprime, hrel⟩, hhom, ?_⟩
  intro I
  constructor
  · intro h p hp
    exact hle (h hp)
  · intro h
    exact (Ideal.homogeneousCore.gc (homogeneousSubmodule S K) I J).mp h

end AlgebraicGeometry.Proj
