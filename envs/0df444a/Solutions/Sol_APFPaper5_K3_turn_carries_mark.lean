-- Prove2me | solution 1 for APFPaper5.K3.turn_carries_mark
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:38:08.391008+00:00
-- url     : https://prove2.me/submissions/807574d6-ffce-4ac1-9fe9-05b1f334ac5d

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_two_mark_continuity
title: The two-mark model satisfies the continuity hypothesis, and its in-between numbers are exactly the pairs that do not commute
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_Continuity and Def_APFPaper5_K3_TwoMarkStates.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
open_hypothesis: hroot, that every nonnegative real is a square. This is a fact of Mathlib (Real.sqrt) whose
 module is not built in the drafting workspace. On a full build replace hroot by
 fun t ht => ⟨Real.sqrt t, Real.mul_self_sqrt ht⟩. Theorems that carry hroot say so in their statement.
statement: (relNumber_is_pair_number) the relation number is the number between the fixed mark and the turned
 mark. (actTurn_carries) the action on held relations is the turn applied to the mark. (relNumber_mem) the
 number lies from 0 to 1. (actTurn_reverse) the reverse turn undoes the turn. (actTurn_join) any held relation
 is turned into any other. (twoMark_turnsLoseNothing) turns lose nothing. (twoMark_rangesOver,
 twoMark_turnsReach, twoMark_continuity; with hroot) the model satisfies the continuity hypothesis on 0 to 1.
 (markP_commutes_iff) the two marks commute exactly when the product of the pair's entries is zero.
 (strictly_between_iff_not_commute) the number is strictly between 0 and 1 exactly when the marks do not commute.
not_claimed: that any interface contains this model; that these turns are admissible on the ledger; any
 complex structure; that the model is the only one satisfying the hypothesis.
-/
import Definitions.Def_APFPaper5_K3_Continuity
import Definitions.Def_APFPaper5_K3_TwoMarkStates
import Theorems.Thm_APFPaper5_K3_pqp
import Theorems.Thm_APFPaper5_K3_turn_carries
import Theorems.Thm_APFPaper5_K3_turn_inverse
import Theorems.Thm_APFPaper5_K3_turn_compose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem relNumber_is_pair_number (w : UnitPair) :
    mul (mul markP (markOf w)) markP = smul (relNumber w) markP :=
  pqp w.1.1 w.1.2

theorem turn_carries_mark (a b u v : ℝ) :
    mul (mul (turn a b) (markQ u v)) (tr (turn a b)) = markQ (a * u - b * v) (b * u + a * v) := by
  apply M2.ext <;> dsimp only [mul, tr, turn, markQ] <;> ring

theorem actTurn_carries (a w : UnitPair) :
    mul (mul (turn a.1.1 a.1.2) (markOf w)) (tr (turn a.1.1 a.1.2)) = markOf (actTurn a w) :=
  turn_carries_mark a.1.1 a.1.2 w.1.1 w.1.2

theorem relNumber_mem (w : UnitPair) : 0 ≤ relNumber w ∧ relNumber w ≤ 1 := by
  obtain ⟨⟨u, v⟩, h⟩ := w
  have h' : u * u + v * v = 1 := h
  show 0 ≤ u * u ∧ u * u ≤ 1
  exact ⟨mul_self_nonneg u, by linarith [mul_self_nonneg v]⟩

theorem actTurn_reverse (a w : UnitPair) : actTurn (reverseTurn a) (actTurn a w) = w := by
  obtain ⟨⟨x, y⟩, ha⟩ := a
  obtain ⟨⟨u, v⟩, hw⟩ := w
  have ha' : x * x + y * y = 1 := ha
  have h1 : (x * x + y * y) * u = u := by rw [ha', one_mul]
  have h2 : (x * x + y * y) * v = v := by rw [ha', one_mul]
  apply Subtype.ext
  apply Prod.ext
  · show x * (x * u - y * v) - (-y) * (y * u + x * v) = u
    linarith
  · show (-y) * (x * u - y * v) + x * (y * u + x * v) = v
    linarith

theorem actTurn_join (s w : UnitPair) : actTurn (actTurn w (reverseTurn s)) s = w := by
  obtain ⟨⟨u, v⟩, hs⟩ := s
  obtain ⟨⟨x, y⟩, hw⟩ := w
  have hs' : u * u + v * v = 1 := hs
  have h1 : x * (u * u + v * v) = x := by rw [hs', mul_one]
  have h2 : y * (u * u + v * v) = y := by rw [hs', mul_one]
  apply Subtype.ext
  apply Prod.ext
  · show (x * u - y * (-v)) * u - (y * u + x * (-v)) * v = x
    linarith
  · show (y * u + x * (-v)) * u + (x * u - y * (-v)) * v = y
    linarith

theorem twoMark_turnsLoseNothing : TurnsLoseNothing admTurns := by
  rintro f ⟨a, rfl⟩
  exact ⟨actTurn (reverseTurn a), ⟨reverseTurn a, rfl⟩, fun s => actTurn_reverse a s⟩

theorem exists_unitPair_of_number (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ w : UnitPair, relNumber w = t := by
  obtain ⟨r, hr⟩ := hroot t h0
  obtain ⟨r', hr'⟩ := hroot (1 - t) (by linarith)
  exact ⟨⟨(r, r'), by show r * r + r' * r' = 1; linarith⟩, hr⟩

theorem twoMark_rangesOver (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t) :
    RangesOverInterval relNumber 0 1 :=
  ⟨zero_lt_one, fun t h0 h1 => exists_unitPair_of_number hroot t h0 h1⟩

theorem twoMark_turnsReach (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t) :
    TurnsReach relNumber 0 1 admTurns := by
  intro s t h0 h1
  obtain ⟨w, hw⟩ := exists_unitPair_of_number hroot t h0 h1
  refine ⟨actTurn (actTurn w (reverseTurn s)), ⟨_, rfl⟩, ?_⟩
  rw [actTurn_join]
  exact hw

theorem twoMark_continuity (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t) :
    Continuity relNumber 0 1 admTurns :=
  ⟨twoMark_rangesOver hroot, twoMark_turnsReach hroot, twoMark_turnsLoseNothing⟩

theorem markP_commutes_iff (u v : ℝ) :
    mul markP (markQ u v) = mul (markQ u v) markP ↔ u * v = 0 := by
  constructor
  · intro h
    have hb := congrArg M2.b h
    dsimp only [mul, markP, markQ] at hb
    linarith
  · intro h
    apply M2.ext <;> dsimp only [mul, markP, markQ] <;> linarith

theorem relNumber_strictly_between_iff (w : UnitPair) :
    (0 < relNumber w ∧ relNumber w < 1) ↔ w.1.1 * w.1.2 ≠ 0 := by
  obtain ⟨⟨u, v⟩, h⟩ := w
  have h' : u * u + v * v = 1 := h
  show (0 < u * u ∧ u * u < 1) ↔ u * v ≠ 0
  constructor
  · rintro ⟨h0, h1⟩ huv
    rcases mul_eq_zero.mp huv with hu | hv
    · rw [hu, mul_zero] at h0
      exact lt_irrefl 0 h0
    · rw [hv, mul_zero, add_zero] at h'
      linarith
  · intro huv
    have hu : u ≠ 0 := fun hu => huv (by rw [hu, zero_mul])
    have hv : v ≠ 0 := fun hv => huv (by rw [hv, mul_zero])
    have hu2 : 0 < u * u := mul_self_pos.mpr hu
    have hv2 : 0 < v * v := mul_self_pos.mpr hv
    exact ⟨hu2, by linarith⟩

theorem strictly_between_iff_not_commute (w : UnitPair) :
    (0 < relNumber w ∧ relNumber w < 1) ↔ mul markP (markOf w) ≠ mul (markOf w) markP :=
  (relNumber_strictly_between_iff w).trans (not_congr (markP_commutes_iff w.1.1 w.1.2)).symm

end APFPaper5.K3


theorem solution :
∀ (a b u v : Real),
  @Eq.{1} APFPaper5.K3.M2
    (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) (APFPaper5.K3.markQ u v))
      (APFPaper5.K3.tr (APFPaper5.K3.turn a b)))
    (APFPaper5.K3.markQ
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b v))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a v))) := by
  exact @APFPaper5.K3.turn_carries_mark
