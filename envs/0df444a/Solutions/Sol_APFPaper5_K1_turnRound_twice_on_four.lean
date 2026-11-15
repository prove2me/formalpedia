-- Prove2me | solution 1 for APFPaper5.K1.turnRound_twice_on_four
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:44:45.77707+00:00
-- url     : https://prove2.me/submissions/2b06b1a4-8653-4927-9bc7-9c6768bb587e

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K1_no_half_of_a_quarter_turn
title: In a finite region no rearrangement with turn-overs has the quarter turn of one pair as its double step; two pairs turned together do have such a half
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ordinary mathematics on Def_APFPaper5_K1_Moves (quarterOn), Def_APFPaper5_K1_PairParity (holdStep)
 and Def_APFPaper5_K1_TurnRound; the sign of a permutation (Mathlib). Paper 5 Supplement v7.33:1714-1723
 (the quarter turn comes from a connected family; the pair {I, -I} is the control) and 3670-3674 (exact circle
 closure needs infinite order). FOUNDATION_INPUTS is not consumed.
consumes_inputs: none.
named_hypotheses: none.
statement: (double_step_apply) the double step of a rearrangement with turn-overs, place by place.
 (no_hold_is_half_a_quarter_turn) for two different distinctions d1, d2 of a finite region, no rearrangement
 with turn-overs, taken twice, is the quarter turn of (d1, d2) with every other distinction left as it was.
 The reason is parity: taken twice, a rearrangement is an even permutation of the distinctions, and
 exchanging two is odd. (turnRound_twice_on_four) on four distinctions, turning the region round one place,
 taken twice, is the quarter turn of the pair (2, 0) together with the quarter turn of the pair (3, 1).
 (turnRound_four_times_on_four) taken four times it turns every distinction over.
 (turnRound_on_two_is_the_quarter_turn) on two distinctions it is the quarter turn of the pair.
reading: a hold that moves one pair by a quarter turn (pass 42) cannot be done in two equal halves, in a
 region of any finite size. Two pairs turned together do have a half, on four distinctions. The general
 rule, that the number of pairs turned together must be even at each halving, is not typed here.
not_claimed: anything about maps that are not rearrangements with turn-overs (a map on records that draws a
 reading can be a half when there are at least three distinctions); anything continuous.
-/
import Definitions.Def_APFPaper5_K1_Moves
import Definitions.Def_APFPaper5_K1_TurnRound
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace APFPaper5.K1

theorem double_step_apply {D : Type*} (f : D → Bool) (sigma : D ≃ D) (v : D → Bool) (d : D) :
    holdStep f sigma (holdStep f sigma v) d
      = xor (xor (f d) (f (sigma d))) (v (sigma (sigma d))) := by
  show xor (f d) (xor (f (sigma d)) (v (sigma (sigma d)))) = _
  cases f d <;> cases f (sigma d) <;> cases v (sigma (sigma d)) <;> rfl

theorem no_hold_is_half_a_quarter_turn {D : Type*} [Fintype D] [DecidableEq D] (d1 d2 : D)
    (hne : d1 ≠ d2) (f : D → Bool) (sigma : D ≃ D) :
    ¬ ∀ v : D → Bool, holdStep f sigma (holdStep f sigma v) = quarterOn d1 d2 v := by
  intro h
  have hs : ∀ d : D, sigma (sigma d) = Equiv.swap d1 d2 d := by
    intro d
    by_contra hd
    have h0 := congrFun (h (fun _ => false)) d
    have h1 := congrFun (h (Function.update (fun _ => false) (Equiv.swap d1 d2 d) true)) d
    rw [double_step_apply] at h0 h1
    change xor (xor (f d) (f (sigma d))) false
      = xor (Function.update (fun _ : D => false) d1 true d) false at h0
    change xor (xor (f d) (f (sigma d)))
        (Function.update (fun _ : D => false) (Equiv.swap d1 d2 d) true (sigma (sigma d)))
      = xor (Function.update (fun _ : D => false) d1 true d)
        (Function.update (fun _ : D => false) (Equiv.swap d1 d2 d) true (Equiv.swap d1 d2 d))
      at h1
    rw [Function.update_self, Function.update_of_ne hd] at h1
    revert h0 h1
    generalize xor (f d) (f (sigma d)) = a
    generalize Function.update (fun _ : D => false) d1 true d = u
    cases a <;> cases u <;> decide
  have hperm : (sigma : Equiv.Perm D) * sigma = Equiv.swap d1 d2 := Equiv.ext hs
  have hsign := congrArg Equiv.Perm.sign hperm
  rw [Equiv.Perm.sign_mul, Int.units_mul_self, Equiv.Perm.sign_swap hne] at hsign
  exact absurd hsign (by decide)

theorem turnRound_on_two_is_the_quarter_turn :
    ∀ v : Fin 2 → Bool, turnRound 1 v = quarterOn 1 0 v := by
  decide

theorem turnRound_twice_on_four :
    ∀ v : Fin 4 → Bool, turnRound 3 (turnRound 3 v) = quarterOn 2 0 (quarterOn 3 1 v) := by
  decide

theorem turnRound_four_times_on_four :
    ∀ v : Fin 4 → Bool, (turnRound 3)^[4] v = fun j => !(v j) := by
  decide

end APFPaper5.K1


theorem solution :
∀ (v : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Bool),
  @Eq.{1}
    (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Bool)
    (APFPaper5.K1.turnRound (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (APFPaper5.K1.turnRound (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) v))
    (@APFPaper5.K1.quarterOn.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)))
      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))
      (@APFPaper5.K1.quarterOn.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 3)))
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)))
        v)) := by
  exact @APFPaper5.K1.turnRound_twice_on_four
