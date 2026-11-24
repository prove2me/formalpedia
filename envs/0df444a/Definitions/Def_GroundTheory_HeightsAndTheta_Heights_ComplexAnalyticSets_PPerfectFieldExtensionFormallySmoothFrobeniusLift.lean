-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:24.082044+00:00
-- url     : https://prove2.me/theorems/48a82e48-0007-4c35-8d0b-29ba90102365
-- title:
--   PPerfect Field Extension Formally Smooth Frobenius Lift
-- statement:
--   Definitions and structural lemmas for PPerfect Field Extension Formally Smooth Frobenius Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothFrobeniusLift.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
section FrobeniusLift
variable {C : Type*} [CommRing C] {N : Ideal C} {p : ℕ}
theorem pow_prime_add_of_sq_eq_bot (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) {n : C}
    (hn : n ∈ N) : (c + n) ^ p = c ^ p := by
  have hn2 : n ^ 2 = 0 := by
    have := Ideal.pow_mem_pow hn 2
    rwa [hN, Ideal.mem_bot] at this
  have hnp : n ^ p = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp.two_le
    rw [hk, pow_add, hn2, zero_mul]
  rw [add_pow_prime_eq hp, hpC, hnp]
  simp
theorem pow_prime_eq_of_mk_eq (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) {c c' : C}
    (h : Ideal.Quotient.mk N c = Ideal.Quotient.mk N c') : c ^ p = c' ^ p := by
  have hmem : c - c' ∈ N := Ideal.Quotient.eq.mp h
  have := pow_prime_add_of_sq_eq_bot hp hpC hN c' hmem
  rwa [add_sub_cancel] at this
noncomputable def sqZeroFrobeniusLift (N : Ideal C) (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) :
    C ⧸ N →+* C where
  toFun y := (Ideal.Quotient.mk_surjective y).choose ^ p
  map_one' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 1) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_one]), one_pow]
  map_mul' x y := by
    rw [← mul_pow]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_mul, (Ideal.Quotient.mk_surjective _).choose_spec])
  map_zero' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 0) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_zero]), zero_pow hp.ne_zero]
  map_add' x y := by
    have hadd : ((Ideal.Quotient.mk_surjective x).choose + (Ideal.Quotient.mk_surjective y).choose) ^ p =
        (Ideal.Quotient.mk_surjective x).choose ^ p + (Ideal.Quotient.mk_surjective y).choose ^ p := by
      rw [add_pow_prime_eq hp, hpC]; simp
    rw [← hadd]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_add, (Ideal.Quotient.mk_surjective _).choose_spec])
end FrobeniusLift
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


