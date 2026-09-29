-- Prove2me | solution 1 for AutomorphicForm.finite_preimage_satakePow_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2d7c0edd-795b-5524-8d2a-a6a79dee94ba

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_preimage_satakePow_pow

set_option autoImplicit false

open AutomorphicForm

namespace SatakeFib

open Polynomial

theorem map_satakePow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (s e : R) :
    φ (satakePow n s e) = satakePow n (φ s) (φ e) := by
  suffices h : ∀ n, φ (satakePow n s e) = satakePow n (φ s) (φ e) ∧
      φ (satakePow (n + 1) s e) = satakePow (n + 1) (φ s) (φ e) from (h n).1
  intro n
  induction n with
  | zero =>
    exact ⟨by rw [satakePow_zero, satakePow_zero, map_ofNat], by rw [satakePow_one, satakePow_one]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [satakePow_add_two, satakePow_add_two, map_sub, map_mul, map_mul, ih.1, ih.2]

noncomputable def satakePoly {R : Type*} [CommRing R] (n : ℕ) (b : R) : R[X] :=
  satakePow n X (C b)

theorem eval_satakePoly {R : Type*} [CommRing R] (n : ℕ) (a b : R) :
    (satakePoly n b).eval a = satakePow n a b := by
  have h := map_satakePow (evalRingHom a) n (X : R[X]) (C b)
  rw [coe_evalRingHom, eval_X, eval_C] at h
  exact h

theorem monic_satakePoly {R : Type*} [CommRing R] [Nontrivial R] (b : R) :
    ∀ n, (satakePoly n b).natDegree ≤ n ∧ (satakePoly (n + 1) b).Monic ∧
      (satakePoly (n + 1) b).natDegree = n + 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show (satakePow 0 X (C b) : R[X]).natDegree ≤ 0
      rw [satakePow_zero]
      exact (natDegree_ofNat (R := R) 2).le
    · show (satakePow 1 X (C b) : R[X]).Monic
      rw [satakePow_one]; exact monic_X
    · show (satakePow 1 X (C b) : R[X]).natDegree = 0 + 1
      rw [satakePow_one, natDegree_X]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hmul : (X * satakePoly (n + 1) b).Monic := monic_X.mul h1
    have hdeg : (X * satakePoly (n + 1) b).natDegree = n + 2 := by
      rw [monic_X.natDegree_mul h1, natDegree_X, h2]; ring
    have hlt : (C b * satakePoly n b).natDegree < (X * satakePoly (n + 1) b).natDegree := by
      rw [hdeg]; exact (natDegree_C_mul_le b _).trans_lt (by omega)
    have e : satakePoly (n + 1 + 1) b = X * satakePoly (n + 1) b - C b * satakePoly n b :=
      satakePow_add_two n X (C b)
    refine ⟨h2.le, ?_, ?_⟩
    · rw [e]; exact hmul.sub_of_left (degree_lt_degree hlt)
    · rw [e, natDegree_sub_eq_left_of_natDegree_lt hlt, hdeg]

theorem finite_setOf_satakePow_eq {R : Type*} [CommRing R] [IsDomain R] (f : ℕ) (hf : f ≠ 0) (b c : R) :
    {a : R | satakePow f a b = c}.Finite := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨-, hmon, hdeg⟩ := monic_satakePoly b n
  have hlt : (C c).natDegree < (satakePoly (n + 1) b).natDegree := by
    rw [natDegree_C, hdeg]; omega
  have hne : satakePoly (n + 1) b - C c ≠ 0 := by
    intro h0
    have := natDegree_sub_eq_left_of_natDegree_lt hlt
    rw [h0, natDegree_zero, hdeg] at this
    omega
  refine (finite_setOf_isRoot hne).subset fun a ha => ?_
  show (satakePoly (n + 1) b - C c).IsRoot a
  rw [IsRoot, eval_sub, eval_C, eval_satakePoly, sub_eq_zero]
  exact ha

theorem finite_setOf_pow_eq {R : Type*} [CommRing R] [IsDomain R] (f : ℕ) (hf : f ≠ 0) (c : R) :
    {b : R | b ^ f = c}.Finite := by
  have hlt : (C c).degree < ((X : R[X]) ^ f).degree := by
    rw [degree_X_pow]
    exact degree_C_le.trans_lt (by exact_mod_cast Nat.pos_of_ne_zero hf)
  have hne : (X : R[X]) ^ f - C c ≠ 0 := ((monic_X_pow f).sub_of_left hlt).ne_zero
  refine (finite_setOf_isRoot hne).subset fun b hb => ?_
  show ((X : R[X]) ^ f - C c).IsRoot b
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
  exact hb

end SatakeFib

theorem solution {R : Type*} [CommRing R] [IsDomain R]
    (f : ℕ) (hf : f ≠ 0) (c : R × R) :
    ((fun p : R × R => (satakePow f p.1 p.2, p.2 ^ f)) ⁻¹' {c}).Finite := by
  have hB := SatakeFib.finite_setOf_pow_eq f hf c.2
  have hA : (⋃ b ∈ {b : R | b ^ f = c.2}, {a : R | satakePow f a b = c.1}).Finite :=
    hB.biUnion fun b _ => SatakeFib.finite_setOf_satakePow_eq f hf b c.1
  refine (hA.prod hB).subset fun p hp => ?_
  have hp' : (satakePow f p.1 p.2, p.2 ^ f) = c := hp
  have h1 : satakePow f p.1 p.2 = c.1 := congrArg Prod.fst hp'
  have h2 : p.2 ^ f = c.2 := congrArg Prod.snd hp'
  exact ⟨Set.mem_biUnion (x := p.2) h2 h1, h2⟩

end S_AutomorphicForm_finite_preimage_satakePow_pow
end P2MW
export P2MW.S_AutomorphicForm_finite_preimage_satakePow_pow (solution)
