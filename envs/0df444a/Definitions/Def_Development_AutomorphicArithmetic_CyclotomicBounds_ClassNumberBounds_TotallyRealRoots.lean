-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:34.333727+00:00
-- url     : https://prove2.me/theorems/6e5cd2d2-dbff-496a-9e01-dfeecc7ca8fd
-- title:
--   Totally Real Roots
-- statement:
--   Definitions and structural lemmas for Totally Real Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace KStar
section Def
variable {R : Type*} [CommRing R]
noncomputable def nuStar (p : R) (U : Set R) (tr : ℕ) : ℕ∞ :=
  sInf ((fun u => emultiplicity p (u ^ tr - 1)) '' U)
theorem le_nuStar_iff (p : R) (U : Set R) (tr n : ℕ) :
    (n : ℕ∞) ≤ nuStar p U tr ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1 := by
  unfold nuStar
  rw [le_sInf_iff, Set.forall_mem_image]
  exact forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm
noncomputable def nuStarNat (p : R) (U : Set R) (tr : ℕ)
    [DecidablePred fun n : ℕ => ∃ u ∈ U, ¬ p ^ (n + 1) ∣ u ^ tr - 1]
    (h : ∃ n : ℕ, ∃ u ∈ U, ¬ p ^ (n + 1) ∣ u ^ tr - 1) : ℕ :=
  Nat.find h
theorem eq_nuStar_of_forall {p : R} {U : Set R} {tr : ℕ} (m : ℕ∞)
    (hm : ∀ n : ℕ, (n : ℕ∞) ≤ m ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1) : m = nuStar p U tr := by
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (le_nuStar_iff p U tr n).mpr ((hm n).mp hn)
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (hm n).mpr ((le_nuStar_iff p U tr n).mp hn)
end Def
section Domain
variable {R : Type*} [CommRing R] [IsDomain R]
end Domain
section Int
end Int
section Inhabitant
example : nuStar (2 : ℤ) {3} 1 = 1 := by
  refine (eq_nuStar_of_forall 1 fun n => ?_).symm
  simp only [Set.mem_singleton_iff, forall_eq, pow_one]
  norm_num
  constructor
  · intro hn
    interval_cases n <;> norm_num
  · intro h
    by_contra hc
    push Not at hc
    have : (2 : ℤ) ^ 2 ∣ 2 := (pow_dvd_pow 2 (by omega : 2 ≤ n)).trans h
    norm_num at this
end Inhabitant
end KStar


