-- Prove2me | solution 1 for APFPaper5.K3.closing_orbit_does_not_move
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:31:08.562204+00:00
-- url     : https://prove2.me/submissions/f3d8a973-62fc-4d77-8159-42c8d82b2584

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_number_alone_cannot_return
title: A hold that brings a number back cannot have that number alone fix the next one in an order-keeping way; and on an orbit that retraces, a state and its mirror have the same present records and different later ones
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's direction of 2026-11-13 ("1 and 2 can be made compatible"). Paper 5 Supplement
 v7.33:1617-1650 (first-order local completeness "keeps both present comparison and continuation direction").
consumes_inputs: none.
statement: (orbit_rises_of_first_rise, orbit_falls_of_first_fall) if each number of a sequence is an
 order-keeping function of the one before, and the first step rises, every step rises; likewise for a fall.
 (closing_orbit_does_not_move) so if the sequence ever returns to its first number, it never moved.
 (number_alone_does_not_fix_next) for a hold D and the states it passes through: if the states return and
 the number moved on the first step, no order-keeping function gives the number after the hold from the
 number before it.
 (retracing_orbit_reads_earlier, retracing_orbit_same_now_different_later) for states numbered both ways
 from a starting state: if the state n steps back has the same present records as the state n steps on,
 then after the hold the state n steps back reads what the state n steps on read one step earlier; so if
 the records one step earlier and one step later differ, the two have the same present records and
 different records after the hold.
reading: order-keeping stands in for smoothness: a small step of a smooth law in one number keeps order.
not_claimed: that any hold returns, retraces or moves a number at an interface; any K.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3

theorem orbit_rises_of_first_rise (f : ℝ → ℝ) (hf : ∀ x y : ℝ, x < y → f x < f y)
    (u : ℕ → ℝ) (hu : ∀ n : ℕ, u (n + 1) = f (u n)) (h0 : u 0 < u 1) (n : ℕ) :
    u n < u (n + 1) ∧ u 0 < u (n + 1) := by
  induction n with
  | zero => exact ⟨h0, h0⟩
  | succ k ih =>
    have step : u (k + 1) < u (k + 1 + 1) := by
      have t := hf _ _ ih.1
      rw [← hu k, ← hu (k + 1)] at t
      exact t
    exact ⟨step, lt_trans ih.2 step⟩

theorem orbit_falls_of_first_fall (f : ℝ → ℝ) (hf : ∀ x y : ℝ, x < y → f x < f y)
    (u : ℕ → ℝ) (hu : ∀ n : ℕ, u (n + 1) = f (u n)) (h0 : u 1 < u 0) (n : ℕ) :
    u (n + 1) < u n ∧ u (n + 1) < u 0 := by
  induction n with
  | zero => exact ⟨h0, h0⟩
  | succ k ih =>
    have step : u (k + 1 + 1) < u (k + 1) := by
      have t := hf _ _ ih.1
      rw [← hu k, ← hu (k + 1)] at t
      exact t
    exact ⟨step, lt_trans step ih.2⟩

theorem closing_orbit_does_not_move (f : ℝ → ℝ) (hf : ∀ x y : ℝ, x < y → f x < f y)
    (u : ℕ → ℝ) (hu : ∀ n : ℕ, u (n + 1) = f (u n)) (N : ℕ) (hN : u (N + 1) = u 0) :
    u 1 = u 0 := by
  rcases lt_trichotomy (u 0) (u 1) with h | h | h
  · have t := (orbit_rises_of_first_rise f hf u hu h N).2
    rw [hN] at t
    exact absurd t (lt_irrefl _)
  · exact h.symm
  · have t := (orbit_falls_of_first_fall f hf u hu h N).2
    rw [hN] at t
    exact absurd t (lt_irrefl _)

theorem number_alone_does_not_fix_next {X : Type*} (num : X → ℝ) (D : X → X) (o : ℕ → X)
    (ho : ∀ n : ℕ, o (n + 1) = D (o n)) (N : ℕ) (hclose : o (N + 1) = o 0)
    (hmove : num (o 1) ≠ num (o 0)) :
    ¬ ∃ f : ℝ → ℝ, (∀ x y : ℝ, x < y → f x < f y) ∧ ∀ x : X, num (D x) = f (num x) := by
  rintro ⟨f, hf, hdet⟩
  apply hmove
  have hu : ∀ n : ℕ, num (o (n + 1)) = f (num (o n)) := fun n => by rw [ho n, hdet]
  have hN : num (o (N + 1)) = num (o 0) := by rw [hclose]
  exact closing_orbit_does_not_move f hf (fun n => num (o n)) hu N hN

theorem retracing_orbit_reads_earlier {X R : Type*} (now : X → R) (D : X → X) (o : ℤ → X)
    (ho : ∀ n : ℤ, o (n + 1) = D (o n)) (hret : ∀ n : ℤ, now (o (-n)) = now (o n)) (n : ℤ) :
    now (D (o (-n))) = now (o (n - 1)) := by
  have e : -n + 1 = -(n - 1) := by ring
  rw [← ho (-n), e, hret]

theorem retracing_orbit_same_now_different_later {X R : Type*} (now : X → R) (D : X → X)
    (o : ℤ → X) (ho : ∀ n : ℤ, o (n + 1) = D (o n)) (hret : ∀ n : ℤ, now (o (-n)) = now (o n))
    (n : ℤ) (hmove : now (o (n - 1)) ≠ now (o (n + 1))) :
    now (o (-n)) = now (o n) ∧ now (D (o (-n))) ≠ now (D (o n)) := by
  refine ⟨hret n, ?_⟩
  rw [retracing_orbit_reads_earlier now D o ho hret n, ← ho n]
  exact hmove

end APFPaper5.K3


theorem solution :
∀ (f : Real → Real) (hf : ∀ (x y : Real), @LT.lt.{0} Real Real.instLT x y → @LT.lt.{0} Real Real.instLT (f x) (f y))
  (u : Nat → Real)
  (hu :
    ∀ (n : Nat),
      @Eq.{1} Real
        (u
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (f (u n)))
  (N : Nat)
  (hN :
    @Eq.{1} Real
      (u
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (u (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  @Eq.{1} Real (u (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (u (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  exact @APFPaper5.K3.closing_orbit_does_not_move
