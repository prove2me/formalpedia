-- Prove2me | solution 1 for APFPaper5.K3.commonTurn_unseen
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:20:44.200089+00:00
-- url     : https://prove2.me/submissions/cb0edc8d-ccd9-4647-86ec-d043ca74ed80

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_two_components
title: For two held components the common turn is unseen by every record, the turn of one component is seen, and the records are exactly what the common turn leaves alone
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoComponents. Paper 5 Supplement v7.33:1808-1832.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (commonTurn_unseen) a common turn by a unit pair changes none of the four records.
 (records_are_cross_data) the two recombination records are the component costs plus twice a cross term.
 (cross_invariant_under_commonTurn) a common turn leaves both cross terms unchanged.
 (relativeTurn_keeps_own_records) a turn of B alone leaves each component's own cost unchanged.
 (relativeTurn_rotates_cross) but it rotates the pair of cross terms by the same pair.
 (relative_half_turn_seen) and so it is seen: a half turn of B takes the recombination record from 4 to 0.
 (commonQuarter_squares_to_neg, commonQuarter_commutes_common, commonQuarter_commutes_relative) the common
 quarter turn done twice reverses every entry, and it commutes with every common turn and every turn of B.
 (same_records_give_common_turn) if two states have the same cost of A, not zero, and the same two cross
 terms, some common turn by a unit pair carries one to the other.
reading: on this carrier the quarter turn is unseen by records, squares to minus the identity and commutes
 with the turns. The records see everything except the common turn.
not_claimed: that an interface is this model; that the common quarter turn is central among all admitted
 maps (the Supplement requires naturality and generator completeness for that); any K.
-/
import Definitions.Def_APFPaper5_K3_TwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

theorem commonTurn_unseen (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    recA (commonTurn c s h) = recA h ∧ recB (commonTurn c s h) = recB h ∧
      recSum (commonTurn c s h) = recSum h ∧ recQuarter (commonTurn c s h) = recQuarter h := by
  have eA : recA (commonTurn c s h) = (c * c + s * s) * recA h := by
    dsimp only [recA, commonTurn]
    ring
  have eB : recB (commonTurn c s h) = (c * c + s * s) * recB h := by
    dsimp only [recB, commonTurn]
    ring
  have eS : recSum (commonTurn c s h) = (c * c + s * s) * recSum h := by
    dsimp only [recSum, commonTurn]
    ring
  have eQ : recQuarter (commonTurn c s h) = (c * c + s * s) * recQuarter h := by
    dsimp only [recQuarter, commonTurn]
    ring
  rw [eA, eB, eS, eQ, hcs, one_mul, one_mul, one_mul, one_mul]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem records_are_cross_data (h : Held2) :
    recSum h = recA h + recB h + 2 * crossRe h ∧
      recQuarter h = recA h + recB h + 2 * crossIm h := by
  constructor <;> dsimp only [recSum, recQuarter, recA, recB, crossRe, crossIm] <;> ring

theorem cross_invariant_under_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    crossRe (commonTurn c s h) = crossRe h ∧ crossIm (commonTurn c s h) = crossIm h := by
  have eR : crossRe (commonTurn c s h) = (c * c + s * s) * crossRe h := by
    dsimp only [crossRe, commonTurn]
    ring
  have eI : crossIm (commonTurn c s h) = (c * c + s * s) * crossIm h := by
    dsimp only [crossIm, commonTurn]
    ring
  rw [eR, eI, hcs, one_mul, one_mul]
  exact ⟨rfl, rfl⟩

theorem relativeTurn_keeps_own_records (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    recA (relativeTurn c s h) = recA h ∧ recB (relativeTurn c s h) = recB h := by
  have eB : recB (relativeTurn c s h) = (c * c + s * s) * recB h := by
    dsimp only [recB, relativeTurn]
    ring
  refine ⟨rfl, ?_⟩
  rw [eB, hcs, one_mul]

theorem relativeTurn_rotates_cross (c s : ℝ) (h : Held2) :
    crossRe (relativeTurn c s h) = c * crossRe h + s * crossIm h ∧
      crossIm (relativeTurn c s h) = c * crossIm h - s * crossRe h := by
  constructor <;> dsimp only [crossRe, crossIm, relativeTurn] <;> ring

theorem relative_half_turn_seen :
    recSum (relativeTurn (-1) 0 ⟨1, 0, 1, 0⟩) = 0 ∧ recSum ⟨1, 0, 1, 0⟩ = 4 := by
  constructor <;> dsimp only [recSum, relativeTurn] <;> norm_num

theorem commonQuarter_squares_to_neg (h : Held2) :
    commonTurn 0 1 (commonTurn 0 1 h) = neg2 h := by
  apply Held2.ext <;> dsimp only [commonTurn, neg2] <;> ring

theorem commonQuarter_commutes_common (c s : ℝ) (h : Held2) :
    commonTurn 0 1 (commonTurn c s h) = commonTurn c s (commonTurn 0 1 h) := by
  apply Held2.ext <;> dsimp only [commonTurn] <;> ring

theorem commonQuarter_commutes_relative (c s : ℝ) (h : Held2) :
    commonTurn 0 1 (relativeTurn c s h) = relativeTurn c s (commonTurn 0 1 h) := by
  apply Held2.ext <;> dsimp only [commonTurn, relativeTurn] <;> ring

theorem same_records_give_common_turn (h h' : Held2) (hA : recA h ≠ 0)
    (h1 : recA h' = recA h) (h2 : crossRe h' = crossRe h) (h3 : crossIm h' = crossIm h) :
    ∃ c s : ℝ, c * c + s * s = 1 ∧ commonTurn c s h = h' := by
  obtain ⟨a1, a2, b1, b2⟩ := h
  obtain ⟨p1, p2, q1, q2⟩ := h'
  dsimp only [recA, crossRe, crossIm] at hA h1 h2 h3
  refine ⟨(a1 * p1 + a2 * p2) / (a1 * a1 + a2 * a2), (a1 * p2 - a2 * p1) / (a1 * a1 + a2 * a2),
    ?_, ?_⟩
  · have e : (a1 * p1 + a2 * p2) * (a1 * p1 + a2 * p2) + (a1 * p2 - a2 * p1) * (a1 * p2 - a2 * p1) =
        (a1 * a1 + a2 * a2) * (p1 * p1 + p2 * p2) := by ring
    rw [div_mul_div_comm, div_mul_div_comm, ← add_div, e, h1]
    exact div_self (mul_ne_zero hA hA)
  · have k1 : (a1 * p1 + a2 * p2) * a1 - (a1 * p2 - a2 * p1) * a2 = (a1 * a1 + a2 * a2) * p1 := by
      ring
    have k2 : (a1 * p2 - a2 * p1) * a1 + (a1 * p1 + a2 * p2) * a2 = (a1 * a1 + a2 * a2) * p2 := by
      ring
    have k3 : (a1 * p1 + a2 * p2) * b1 - (a1 * p2 - a2 * p1) * b2 = (a1 * a1 + a2 * a2) * q1 := by
      have e1 : (a1 * p1 + a2 * p2) * b1 - (a1 * p2 - a2 * p1) * b2 =
          p1 * (a1 * b1 + a2 * b2) + p2 * (a2 * b1 - a1 * b2) := by ring
      rw [e1, ← h2, ← h3, ← h1]
      ring
    have k4 : (a1 * p2 - a2 * p1) * b1 + (a1 * p1 + a2 * p2) * b2 = (a1 * a1 + a2 * a2) * q2 := by
      have e1 : (a1 * p2 - a2 * p1) * b1 + (a1 * p1 + a2 * p2) * b2 =
          p2 * (a1 * b1 + a2 * b2) - p1 * (a2 * b1 - a1 * b2) := by ring
      rw [e1, ← h2, ← h3, ← h1]
      ring
    apply Held2.ext
    · show (a1 * p1 + a2 * p2) / (a1 * a1 + a2 * a2) * a1 -
        (a1 * p2 - a2 * p1) / (a1 * a1 + a2 * a2) * a2 = p1
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, k1, mul_div_cancel_left₀ _ hA]
    · show (a1 * p2 - a2 * p1) / (a1 * a1 + a2 * a2) * a1 +
        (a1 * p1 + a2 * p2) / (a1 * a1 + a2 * a2) * a2 = p2
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, k2, mul_div_cancel_left₀ _ hA]
    · show (a1 * p1 + a2 * p2) / (a1 * a1 + a2 * a2) * b1 -
        (a1 * p2 - a2 * p1) / (a1 * a1 + a2 * a2) * b2 = q1
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div, k3, mul_div_cancel_left₀ _ hA]
    · show (a1 * p2 - a2 * p1) / (a1 * a1 + a2 * a2) * b1 +
        (a1 * p1 + a2 * p2) / (a1 * a1 + a2 * a2) * b2 = q2
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, k4, mul_div_cancel_left₀ _ hA]

end APFPaper5.K3


theorem solution :
∀ (c s : Real)
  (hcs :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (h : APFPaper5.K3.Held2),
  And (@Eq.{1} Real (APFPaper5.K3.recA (APFPaper5.K3.commonTurn c s h)) (APFPaper5.K3.recA h))
    (And (@Eq.{1} Real (APFPaper5.K3.recB (APFPaper5.K3.commonTurn c s h)) (APFPaper5.K3.recB h))
      (And (@Eq.{1} Real (APFPaper5.K3.recSum (APFPaper5.K3.commonTurn c s h)) (APFPaper5.K3.recSum h))
        (@Eq.{1} Real (APFPaper5.K3.recQuarter (APFPaper5.K3.commonTurn c s h)) (APFPaper5.K3.recQuarter h)))) := by
  exact @APFPaper5.K3.commonTurn_unseen
