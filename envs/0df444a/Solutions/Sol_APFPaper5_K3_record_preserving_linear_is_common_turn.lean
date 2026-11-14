-- Prove2me | solution 1 for APFPaper5.K3.record_preserving_linear_is_common_turn
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:31:59.55389+00:00
-- url     : https://prove2.me/submissions/4806c830-4b81-4a8c-bc96-823f5d752e80

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_quarter_turn_commutes
title: Every additive homogeneous map that preserves all four records is a common turn and commutes with the quarter turn; with the fourth record dropped, the rate flip preserves the rest and does not
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_LinearOnTwoComponents. Paper 5 Supplement v7.33:1988-2032 (descent criterion and
 module closure), 1752-1760 (trivial orientation monodromy), 1958 (reversal as inverse).
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (record_preserving_linear_is_common_turn) if combo u1 u2 u3 u4 leaves the cost of each component
 and both cross terms unchanged at every state, it is the common turn by a unit pair.
 (record_preserving_linear_commutes_with_quarter) so it commutes with the common quarter turn.
 (rateFlip_preserves_plain_records) the rate flip leaves the two component costs and the plain recombination
 record unchanged. (rateFlip_reverses_second_cross) it reverses the second cross term, so the quarter-turned
 recombination record becomes the component costs less twice that cross term.
 (rateFlip_seen_by_quarter_record) and that record does change: from 0 to 4 at one state.
 (rateFlip_anticommutes, rateFlip_does_not_commute) the rate flip followed by the quarter turn is the reverse
 of the quarter turn followed by the rate flip, and the two orders differ at one state.
 (rateFlip_reverses_turn) the rate flip carries the common turn by (c, s) to the common turn by (c, -s).
reading: whether every record-preserving map commutes with the quarter turn depends on one thing: whether
 the quarter-turned recombination is itself a record. If it is, yes. If it is not, the rate flip is a
 counterexample. That record is what the Supplement's module closure supplies.
not_claimed: that the quarter-turned recombination is a record at any interface; centrality among maps that
 change records; generator completeness; any K.
-/
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

theorem record_preserving_linear_is_common_turn (u1 u2 u3 u4 : Held2)
    (hpres : ∀ h : Held2, recA (combo u1 u2 u3 u4 h) = recA h ∧
      recB (combo u1 u2 u3 u4 h) = recB h ∧ crossRe (combo u1 u2 u3 u4 h) = crossRe h ∧
      crossIm (combo u1 u2 u3 u4 h) = crossIm h) :
    ∃ c s : ℝ, c * c + s * s = 1 ∧ ∀ h : Held2, combo u1 u2 u3 u4 h = commonTurn c s h := by
  obtain ⟨x1, y1, z1, w1⟩ := u1
  obtain ⟨x2, y2, z2, w2⟩ := u2
  obtain ⟨x3, y3, z3, w3⟩ := u3
  obtain ⟨x4, y4, z4, w4⟩ := u4
  have hA3 := (hpres ⟨0, 0, 1, 0⟩).1
  have hA4 := (hpres ⟨0, 0, 0, 1⟩).1
  have hB1 := (hpres ⟨1, 0, 0, 0⟩).2.1
  have hB2 := (hpres ⟨0, 1, 0, 0⟩).2.1
  dsimp only [combo, recA, recB] at hA3 hA4 hB1 hB2
  have hx3 : x3 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg x3, mul_self_nonneg y3])
  have hy3 : y3 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg x3, mul_self_nonneg y3])
  have hx4 : x4 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg x4, mul_self_nonneg y4])
  have hy4 : y4 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg x4, mul_self_nonneg y4])
  have hz1 : z1 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg z1, mul_self_nonneg w1])
  have hw1 : w1 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg z1, mul_self_nonneg w1])
  have hz2 : z2 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg z2, mul_self_nonneg w2])
  have hw2 : w2 = 0 := mul_self_eq_zero.mp (by linarith [mul_self_nonneg z2, mul_self_nonneg w2])
  subst hx3 hy3 hx4 hy4 hz1 hw1 hz2 hw2
  have hA1 := (hpres ⟨1, 0, 0, 0⟩).1
  have hB3 := (hpres ⟨0, 0, 1, 0⟩).2.1
  have hR13 := (hpres ⟨1, 0, 1, 0⟩).2.2.1
  have hR14 := (hpres ⟨1, 0, 0, 1⟩).2.2.1
  have hI14 := (hpres ⟨1, 0, 0, 1⟩).2.2.2
  have hR23 := (hpres ⟨0, 1, 1, 0⟩).2.2.1
  have hI23 := (hpres ⟨0, 1, 1, 0⟩).2.2.2
  dsimp only [combo, recA, recB, crossRe, crossIm] at hA1 hB3 hR13 hR14 hI14 hR23 hI23
  have F5 : x1 * x1 + y1 * y1 = 1 := by linarith
  have F6 : z3 * z3 + w3 * w3 = 1 := by linarith
  have F7 : x1 * z3 + y1 * w3 = 1 := by linarith
  have F9 : x1 * z4 + y1 * w4 = 0 := by linarith
  have F10 : y1 * z4 - x1 * w4 = -1 := by linarith
  have F11r : x2 * z3 + y2 * w3 = 0 := by linarith
  have F12r : y2 * z3 - x2 * w3 = 1 := by linarith
  have hsq : (x1 - z3) * (x1 - z3) + (y1 - w3) * (y1 - w3) = 0 := by linarith
  have hz3 : z3 = x1 := by
    have h := mul_self_eq_zero.mp
      (show (x1 - z3) * (x1 - z3) = 0 by
        linarith [mul_self_nonneg (x1 - z3), mul_self_nonneg (y1 - w3)])
    linarith
  have hw3 : w3 = y1 := by
    have h := mul_self_eq_zero.mp
      (show (y1 - w3) * (y1 - w3) = 0 by
        linarith [mul_self_nonneg (x1 - z3), mul_self_nonneg (y1 - w3)])
    linarith
  have F11 : x2 * x1 + y2 * y1 = 0 := by
    rw [hz3, hw3] at F11r
    exact F11r
  have F12 : y2 * x1 - x2 * y1 = 1 := by
    rw [hz3, hw3] at F12r
    exact F12r
  have hz4 : z4 = -y1 := by
    have e : (x1 * x1 + y1 * y1) * z4 = x1 * (x1 * z4 + y1 * w4) + y1 * (y1 * z4 - x1 * w4) := by
      ring
    rw [F5, F9, F10] at e
    linarith
  have hw4 : w4 = x1 := by
    have e : (x1 * x1 + y1 * y1) * w4 = y1 * (x1 * z4 + y1 * w4) - x1 * (y1 * z4 - x1 * w4) := by
      ring
    rw [F5, F9, F10] at e
    linarith
  have hx2 : x2 = -y1 := by
    have e : (x1 * x1 + y1 * y1) * x2 = x1 * (x2 * x1 + y2 * y1) - y1 * (y2 * x1 - x2 * y1) := by
      ring
    rw [F5, F11, F12] at e
    linarith
  have hy2 : y2 = x1 := by
    have e : (x1 * x1 + y1 * y1) * y2 = y1 * (x2 * x1 + y2 * y1) + x1 * (y2 * x1 - x2 * y1) := by
      ring
    rw [F5, F11, F12] at e
    linarith
  refine ⟨x1, y1, F5, fun h => ?_⟩
  rw [hz3, hw3, hz4, hw4, hx2, hy2]
  apply Held2.ext <;> dsimp only [combo, commonTurn] <;> ring

theorem record_preserving_linear_commutes_with_quarter (u1 u2 u3 u4 : Held2)
    (hpres : ∀ h : Held2, recA (combo u1 u2 u3 u4 h) = recA h ∧
      recB (combo u1 u2 u3 u4 h) = recB h ∧ crossRe (combo u1 u2 u3 u4 h) = crossRe h ∧
      crossIm (combo u1 u2 u3 u4 h) = crossIm h) (h : Held2) :
    commonTurn 0 1 (combo u1 u2 u3 u4 h) = combo u1 u2 u3 u4 (commonTurn 0 1 h) := by
  obtain ⟨c, s, _, hL⟩ := record_preserving_linear_is_common_turn u1 u2 u3 u4 hpres
  rw [hL, hL, commonQuarter_commutes_common]

theorem rateFlip_preserves_plain_records (h : Held2) :
    recA (rateFlip h) = recA h ∧ recB (rateFlip h) = recB h ∧ recSum (rateFlip h) = recSum h := by
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only [recA, recB, recSum, rateFlip] <;> ring

theorem rateFlip_reverses_second_cross (h : Held2) :
    crossRe (rateFlip h) = crossRe h ∧ crossIm (rateFlip h) = -crossIm h ∧
      recQuarter (rateFlip h) = recA h + recB h - 2 * crossIm h := by
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp only [crossRe, crossIm, recQuarter, recA, recB, rateFlip] <;> ring

theorem rateFlip_seen_by_quarter_record :
    recQuarter ⟨1, 0, 0, 1⟩ = 0 ∧ recQuarter (rateFlip ⟨1, 0, 0, 1⟩) = 4 := by
  constructor <;> dsimp only [recQuarter, rateFlip] <;> norm_num

theorem rateFlip_anticommutes (h : Held2) :
    commonTurn 0 1 (rateFlip h) = neg2 (rateFlip (commonTurn 0 1 h)) := by
  apply Held2.ext <;> dsimp only [commonTurn, rateFlip, neg2] <;> ring

theorem rateFlip_does_not_commute :
    commonTurn 0 1 (rateFlip ⟨1, 0, 0, 0⟩) ≠ rateFlip (commonTurn 0 1 ⟨1, 0, 0, 0⟩) := by
  intro hc
  have h2 := congrArg Held2.a2 hc
  dsimp only [commonTurn, rateFlip] at h2
  norm_num at h2

theorem rateFlip_reverses_turn (c s : ℝ) (h : Held2) :
    rateFlip (commonTurn c s h) = commonTurn c (-s) (rateFlip h) := by
  apply Held2.ext <;> dsimp only [commonTurn, rateFlip] <;> ring

end APFPaper5.K3


theorem solution :
∀ (u1 u2 u3 u4 : APFPaper5.K3.Held2)
  (hpres :
    ∀ (h : APFPaper5.K3.Held2),
      And (@Eq.{1} Real (APFPaper5.K3.recA (APFPaper5.K3.combo u1 u2 u3 u4 h)) (APFPaper5.K3.recA h))
        (And (@Eq.{1} Real (APFPaper5.K3.recB (APFPaper5.K3.combo u1 u2 u3 u4 h)) (APFPaper5.K3.recB h))
          (And (@Eq.{1} Real (APFPaper5.K3.crossRe (APFPaper5.K3.combo u1 u2 u3 u4 h)) (APFPaper5.K3.crossRe h))
            (@Eq.{1} Real (APFPaper5.K3.crossIm (APFPaper5.K3.combo u1 u2 u3 u4 h)) (APFPaper5.K3.crossIm h))))),
  @Exists.{1} Real fun (c : Real) =>
    @Exists.{1} Real fun (s : Real) =>
      And
        (@Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (∀ (h : APFPaper5.K3.Held2),
          @Eq.{1} APFPaper5.K3.Held2 (APFPaper5.K3.combo u1 u2 u3 u4 h) (APFPaper5.K3.commonTurn c s h)) := by
  exact @APFPaper5.K3.record_preserving_linear_is_common_turn
