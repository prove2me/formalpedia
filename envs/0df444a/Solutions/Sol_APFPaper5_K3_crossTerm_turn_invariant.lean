-- Prove2me | solution 1 for APFPaper5.K3.crossTerm_turn_invariant
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:21:23.289578+00:00
-- url     : https://prove2.me/submissions/99897204-f6cf-4b11-a71e-2a2e99a98e8d

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_two_mark_cross_term
title: In the two-mark model the pair number is the cross term of the sum-of-squares cost, and turning both marks together leaves it unchanged
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkCost. The test announced in NOTE_derivation_pass_2_2026-11-12.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (sqCost_add) the cost of two arrays together is the sum of their costs plus twice the cross term.
 (crossTerm_symm) the cross term is symmetric. (pair_number_is_cross_term) for any array q the word fixed
 mark, q, fixed mark is the cross term of the fixed mark and q, times the fixed mark.
 (crossTerm_markP_markQ) the cross term of the fixed mark and the turned mark is u * u. (sqCost_markP,
 sqCost_markQ) each mark costs 1. (sqCost_turn_invariant, crossTerm_turn_invariant) a turn applied to an array
 leaves its cost unchanged, and a turn applied to both arrays leaves their cross term unchanged.
reading: the candidate "number = cross term of the cost" returns the square in this model. The joint fraction
 does not (Thm_APFPaper1_joint_fraction_exclusive).
-/
import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3

theorem sqCost_add (x y : M2) : sqCost (add x y) = sqCost x + sqCost y + 2 * crossTerm x y := by
  dsimp only [sqCost, add, crossTerm]
  ring

theorem crossTerm_symm (x y : M2) : crossTerm x y = crossTerm y x := by
  dsimp only [crossTerm]
  ring

theorem pair_number_is_cross_term (q : M2) :
    mul (mul markP q) markP = smul (crossTerm markP q) markP := by
  apply M2.ext <;> dsimp only [mul, smul, markP, crossTerm] <;> ring

theorem crossTerm_markP_markQ (u v : ℝ) : crossTerm markP (markQ u v) = u * u := by
  dsimp only [crossTerm, markP, markQ]
  ring

theorem sqCost_markP : sqCost markP = 1 := by
  dsimp only [sqCost, markP]
  ring

theorem sqCost_markQ (u v : ℝ) (h : u * u + v * v = 1) : sqCost (markQ u v) = 1 := by
  have e : sqCost (markQ u v) = (u * u + v * v) * (u * u + v * v) := by
    dsimp only [sqCost, markQ]
    ring
  rw [e, h, mul_one]

theorem sqCost_turn_invariant (a b : ℝ) (h : a * a + b * b = 1) (x : M2) :
    sqCost (mul (mul (turn a b) x) (tr (turn a b))) = sqCost x := by
  have e : sqCost (mul (mul (turn a b) x) (tr (turn a b))) =
      (a * a + b * b) * (a * a + b * b) * sqCost x := by
    dsimp only [sqCost, mul, tr, turn]
    ring
  rw [e, h, mul_one, one_mul]

theorem crossTerm_turn_invariant (a b : ℝ) (h : a * a + b * b = 1) (x y : M2) :
    crossTerm (mul (mul (turn a b) x) (tr (turn a b))) (mul (mul (turn a b) y) (tr (turn a b))) =
      crossTerm x y := by
  have e : crossTerm (mul (mul (turn a b) x) (tr (turn a b)))
        (mul (mul (turn a b) y) (tr (turn a b))) =
      (a * a + b * b) * (a * a + b * b) * crossTerm x y := by
    dsimp only [crossTerm, mul, tr, turn]
    ring
  rw [e, h, mul_one, one_mul]

end APFPaper5.K3


theorem solution :
∀ (a b : Real)
  (h :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a a)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b b))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (x y : APFPaper5.K3.M2),
  @Eq.{1} Real
    (APFPaper5.K3.crossTerm
      (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) x) (APFPaper5.K3.tr (APFPaper5.K3.turn a b)))
      (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) y) (APFPaper5.K3.tr (APFPaper5.K3.turn a b))))
    (APFPaper5.K3.crossTerm x y) := by
  exact @APFPaper5.K3.crossTerm_turn_invariant
