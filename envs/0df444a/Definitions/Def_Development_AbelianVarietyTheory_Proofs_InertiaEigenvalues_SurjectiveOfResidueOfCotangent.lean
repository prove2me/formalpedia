-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SurjectiveOfResidueOfCotangent
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SurjectiveOfResidueOfCotangent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:40.317695+00:00
-- url     : https://prove2.me/theorems/3d45a098-369e-4829-bc5f-78b2001753e2
-- title:
--   Surjective Of Residue Of Cotangent
-- statement:
--   Definitions and structural lemmas for Surjective Of Residue Of Cotangent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SurjectiveOfResidueOfCotangent.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix TensorProduct
namespace GlobalTheory.LocalSurj
theorem exists_sub_mem_map_pow_succ {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (n : ℕ) (a : A)
    (ha : a ∈ (m ^ n).map f) : ∃ x ∈ m ^ n, a - f x ∈ (m ^ (n + 1)).map f := by
  change a ∈ Ideal.span (f '' ((m ^ n : Ideal R) : Set R)) at ha
  induction ha using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨x', hx2, hx2'⟩ := hz
    refine ⟨x + x', add_mem hx hx2, ?_⟩
    have : y + z - f (x + x') = (y - f x) + (z - f x') := by rw [map_add]; ring
    rw [this]; exact add_mem hx' hx2'
  | smul c y _ hy =>
    obtain ⟨x, hx, hx'⟩ := hy
    obtain ⟨s, hs⟩ := hm c
    refine ⟨s * x, Ideal.mul_mem_left _ _ hx, ?_⟩
    have : c • y - f (s * x) = c * (y - f x) + (c - f s) * f x := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    refine add_mem (Ideal.mul_mem_left _ _ hx') ?_
    rw [pow_succ', Ideal.map_mul]
    exact Ideal.mul_mem_mul hs (Ideal.mem_map_of_mem f hx)
noncomputable def approx {R A : Type} [CommRing R] [CommRing A] (f : R →+* A)
    (m : Ideal R) (hm : ∀ z : A, ∃ r, z - f r ∈ m.map f) (a : A) :
    (n : ℕ) → {x : R // a - f x ∈ (m ^ n).map f}
  | 0 => ⟨0, by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; trivial⟩
  | n + 1 =>
    let p := approx f m hm a n
    let h := exists_sub_mem_map_pow_succ f m hm n _ p.2
    ⟨p.1 + h.choose, by
      have := h.choose_spec.2
      rwa [map_add, ← sub_sub]⟩
end GlobalTheory.LocalSurj


