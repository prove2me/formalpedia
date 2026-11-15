-- Prove2me | solution 1 for APFPaper5.K1.no_hold_is_half_a_quarter_turn
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:44:16.765579+00:00
-- url     : https://prove2.me/submissions/44757f99-ba0d-4eee-875e-82d078b6b8bd

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


universe apfNative_u_1
theorem solution :
∀ {D : Type apfNative_u_1} [Fintype.{apfNative_u_1} D] [inst : DecidableEq.{apfNative_u_1 + 1} D] (d1 d2 : D)
  (hne : @Ne.{apfNative_u_1 + 1} D d1 d2) (f : D → Bool) (sigma : Equiv.{apfNative_u_1 + 1, apfNative_u_1 + 1} D D),
  Not
    (∀ (v : D → Bool),
      @Eq.{apfNative_u_1 + 1} (D → Bool)
        (@APFPaper5.K1.holdStep.{apfNative_u_1} D f sigma (@APFPaper5.K1.holdStep.{apfNative_u_1} D f sigma v))
        (@APFPaper5.K1.quarterOn.{apfNative_u_1} D inst d1 d2 v)) := by
  exact @APFPaper5.K1.no_hold_is_half_a_quarter_turn
