-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FrobFixNegOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:14.627109+00:00
-- url     : https://prove2.me/theorems/c5cb7962-807c-4ee3-bc56-d1a827afb2e1
-- title:
--   Frob Fix Neg One
-- statement:
--   Definitions and structural lemmas for Frob Fix Neg One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FrobFixNegOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
section General
variable {R : Type*} [CommRing R] (p : ℕ)
def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x
variable {p}
theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2
theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  · have h := frobFix_iter h1 (f2 - 1)
    rwa [Nat.sub_add_cancel hf2] at h
  · have h := frobFix_iter h2 (f1 - 1)
    rwa [Nat.sub_add_cancel hf1, mul_comm] at h
theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p (x * y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h
theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p (x + y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have h3 := frobFix_add_lemma hp x y f
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add h3 h1) h2
theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  refine ⟨1, one_pos, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  · rw [pow_one, hodd.neg_one_pow, sub_self]
    exact dvd_zero _
theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p (-x) := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx
theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩
theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩
def frobFixSubring (R : Type*) [CommRing R] (hp : p.Prime) : Subring R where
  carrier := {x | FrobFix p x}
  mul_mem' := frobFix_mul
  one_mem' := frobFix_one
  add_mem' := frobFix_add hp
  zero_mem' := frobFix_zero hp
  neg_mem' := frobFix_neg hp
end General
variable (l : ℕ) [Fact l.Prime]
end ReciprocityTheory.ChartRestriction.L1


