-- Prove2me | solution 1 for APFPaper5.K3.quarter_turn_squares_to_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:24:18.723199+00:00
-- url     : https://prove2.me/submissions/477101f5-f127-4b74-9786-0ae252af43fe

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_turns_are_complex_units
title: In the two-mark model the quarter turn squares to minus the identity, commutes with every turn, and every turn is a combination of the identity and the quarter turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkModel and Def_APFPaper5_K3_TwoMarkCost. Archive APFNativeG1.G1_04 (two
 exchanges compose to a turn, and in the elliptic case give a map squaring to minus the identity). Paper 5
 Supplement v7.33:1621-1647 and 1940-1960 (the plane of value and rate; local J squared equal to minus the
 identity does not imply global centrality).
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (quarter_turn_squares_to_minus_one) the quarter turn done twice is minus the identity.
 (turns_commute) any two turns commute. (turn_is_combination) the turn by (a, b) is a times the identity plus b
 times the quarter turn.
reading: the plane of amplitude pairs already carries the arithmetic of the complex numbers, with the quarter
 turn as the square root of minus one.
not_claimed: that the quarter turn is unseen by records. In this model it is seen: it exchanges the two
 exclusive marks. The Supplement's complex structure sits on a different carrier, the value and rate of one
 held component, and needs the common phase to be unseen. That is not shown here.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3

theorem quarter_turn_squares_to_minus_one : mul (turn 0 1) (turn 0 1) = smul (-1) one := by
  apply M2.ext <;> dsimp only [mul, turn, smul, one] <;> ring

theorem turns_commute (a b c d : ℝ) : mul (turn a b) (turn c d) = mul (turn c d) (turn a b) := by
  apply M2.ext <;> dsimp only [mul, turn] <;> ring

theorem turn_is_combination (a b : ℝ) : turn a b = add (smul a one) (smul b (turn 0 1)) := by
  apply M2.ext <;> dsimp only [turn, add, smul, one] <;> ring

end APFPaper5.K3


theorem solution :
@Eq.{1} APFPaper5.K3.M2
  (APFPaper5.K3.mul
    (APFPaper5.K3.turn (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (APFPaper5.K3.turn (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (APFPaper5.K3.smul
    (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    APFPaper5.K3.one) := by
  exact @APFPaper5.K3.quarter_turn_squares_to_minus_one
