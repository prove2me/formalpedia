-- Prove2me | solution 1 for APFPaper5.K3.records_of_plainAfterTurn_eq
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:18:31.580971+00:00
-- url     : https://prove2.me/submissions/92fdfc5d-ddec-4780-8734-3903704b461b

import Theorems.Thm_APFPaper5_K3_cross_invariant_under_commonTurn
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_determines_plain
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_determines_quarter
import Theorems.Thm_APFPaper5_K3_recSum_after_relative_turn
import Theorems.Thm_APFPaper5_K3_relativeTurn_keeps_own_records
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_unseen_dichotomy
title: The common turn stays unseen after an additive homogeneous map exactly when the map commutes or anticommutes with the quarter turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_HeldMaps. The test announced in NOTE_derivation_pass_9_2026-11-13.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (plainAfterTurn_eq_iff_records) two states have the same continuation profile exactly when their
 two costs and two cross terms agree.
 (pair_dichotomy) if w has the costs and cross terms of v, and so has one further combination of v and w,
 then w is the quarter turn of v or its reverse.
 (unseen_dichotomy) an additive homogeneous map after which the common turn is unseen commutes with the
 quarter turn or anticommutes with it.
 (unseen_of_commutes, unseen_of_anticommutes, unseen_iff) and conversely.
 (square_commutes_quarter) the square of such a map commutes with the quarter turn.
 (unseen_of_fixed_by_records) if the two costs and two cross terms after a map are fixed by the two costs and
 two cross terms before it, the common turn is unseen after it. This is the first-order clause read on this
 carrier: what follows is fixed by the costs, the number and its rate.
not_claimed: that the common turn is unseen after every admitted map at an interface; that admitted maps are
 additive and homogeneous there; any K.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFB01_quarter_record_descends
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

theorem plainAfterTurn_eq_of_records (h h' : Held2) (hA : recA h = recA h') (hB : recB h = recB h')
    (hRe : crossRe h = crossRe h') (hIm : crossIm h = crossIm h') :
    plainAfterTurn h = plainAfterTurn h' := by
  funext x
  unfold plainAfterTurn
  have key : ∀ k k' : Held2, recA k = recA k' → recB k = recB k' → crossRe k = crossRe k' →
      crossIm k = crossIm k' → x.1 * x.1 + x.2.1 * x.2.1 = 1 →
      (recA (relativeTurn x.1 x.2.1 k), recB (relativeTurn x.1 x.2.1 k),
        recSum (relativeTurn x.1 x.2.1 k)) =
      (recA (relativeTurn x.1 x.2.1 k'), recB (relativeTurn x.1 x.2.1 k'),
        recSum (relativeTurn x.1 x.2.1 k')) := by
    intro k k' kA kB kRe kIm hu
    obtain ⟨e1, e2⟩ := relativeTurn_keeps_own_records x.1 x.2.1 hu k
    obtain ⟨f1, f2⟩ := relativeTurn_keeps_own_records x.1 x.2.1 hu k'
    rw [e1, e2, f1, f2, recSum_after_relative_turn, recSum_after_relative_turn, kA, kB, kRe, kIm]
  apply propext
  constructor
  · rintro ⟨hu, he⟩
    exact ⟨hu, he.trans (key h h' hA hB hRe hIm hu)⟩
  · rintro ⟨hu, he⟩
    exact ⟨hu, he.trans (key h h' hA hB hRe hIm hu).symm⟩

theorem records_of_plainAfterTurn_eq (h h' : Held2) (hprof : plainAfterTurn h = plainAfterTurn h') :
    recA h = recA h' ∧ recB h = recB h' ∧ crossRe h = crossRe h' ∧ crossIm h = crossIm h' := by
  obtain ⟨hA, hB, hS⟩ := plainAfterTurn_determines_plain h h' hprof
  have hQ := plainAfterTurn_determines_quarter h h' hprof
  obtain ⟨e1, e2⟩ := records_are_cross_data h
  obtain ⟨f1, f2⟩ := records_are_cross_data h'
  refine ⟨hA, hB, ?_, ?_⟩
  · linarith
  · linarith

theorem plainAfterTurn_eq_iff_records (h h' : Held2) :
    plainAfterTurn h = plainAfterTurn h' ↔
      recA h = recA h' ∧ recB h = recB h' ∧ crossRe h = crossRe h' ∧ crossIm h = crossIm h' :=
  ⟨records_of_plainAfterTurn_eq h h', fun ⟨hA, hB, hRe, hIm⟩ =>
    plainAfterTurn_eq_of_records h h' hA hB hRe hIm⟩

theorem pair_dichotomy (v w : Held2) (hA : recA w = recA v) (hB : recB w = recB v)
    (hRe : crossRe w = crossRe v) (hIm : crossIm w = crossIm v)
    (hA' : recA (add2 (smul2 (3 / 5) v) (smul2 (4 / 5) w)) = recA v)
    (hB' : recB (add2 (smul2 (3 / 5) v) (smul2 (4 / 5) w)) = recB v) :
    w = commonTurn 0 1 v ∨ w = neg2 (commonTurn 0 1 v) := by
  obtain ⟨p1, p2, p3, p4⟩ := v
  obtain ⟨q1, q2, q3, q4⟩ := w
  dsimp only [recA, recB, crossRe, crossIm, add2, smul2] at hA hB hRe hIm hA' hB'
  have F1 : p1 * q1 + p2 * q2 = 0 := by linear_combination (25 / 24) * hA' - (2 / 3) * hA
  have F2 : p3 * q3 + p4 * q4 = 0 := by linear_combination (25 / 24) * hB' - (2 / 3) * hB
  have S1 : (p1 * q2 - p2 * q1 - (p1 * p1 + p2 * p2)) * (p1 * q2 - p2 * q1 + (p1 * p1 + p2 * p2)) = 0 := by
    linear_combination (p1 * p1 + p2 * p2) * hA - (p1 * q1 + p2 * q2) * F1
  have S2 : (p3 * q4 - p4 * q3 - (p3 * p3 + p4 * p4)) * (p3 * q4 - p4 * q3 + (p3 * p3 + p4 * p4)) = 0 := by
    linear_combination (p3 * p3 + p4 * p4) * hB - (p3 * q3 + p4 * q4) * F2
  have plus1 : p1 * q2 - p2 * q1 - (p1 * p1 + p2 * p2) = 0 → q1 = -p2 ∧ q2 = p1 := by
    intro hs
    have hz : (q1 + p2) * (q1 + p2) + (q2 - p1) * (q2 - p1) = 0 := by linear_combination hA - 2 * hs
    obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp hz
    exact ⟨by linarith, by linarith⟩
  have minus1 : p1 * q2 - p2 * q1 + (p1 * p1 + p2 * p2) = 0 → q1 = p2 ∧ q2 = -p1 := by
    intro hs
    have hz : (q1 - p2) * (q1 - p2) + (q2 + p1) * (q2 + p1) = 0 := by linear_combination hA + 2 * hs
    obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp hz
    exact ⟨by linarith, by linarith⟩
  have plus2 : p3 * q4 - p4 * q3 - (p3 * p3 + p4 * p4) = 0 → q3 = -p4 ∧ q4 = p3 := by
    intro hs
    have hz : (q3 + p4) * (q3 + p4) + (q4 - p3) * (q4 - p3) = 0 := by linear_combination hB - 2 * hs
    obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp hz
    exact ⟨by linarith, by linarith⟩
  have minus2 : p3 * q4 - p4 * q3 + (p3 * p3 + p4 * p4) = 0 → q3 = p4 ∧ q4 = -p3 := by
    intro hs
    have hz : (q3 - p4) * (q3 - p4) + (q4 + p3) * (q4 + p3) = 0 := by linear_combination hB + 2 * hs
    obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp hz
    exact ⟨by linarith, by linarith⟩
  have left_of : q1 = -p2 → q2 = p1 → q3 = -p4 → q4 = p3 →
      (⟨q1, q2, q3, q4⟩ : Held2) = commonTurn 0 1 ⟨p1, p2, p3, p4⟩ := by
    intro e1 e2 e3 e4
    apply Held2.ext <;> dsimp only [commonTurn] <;> linarith
  have right_of : q1 = p2 → q2 = -p1 → q3 = p4 → q4 = -p3 →
      (⟨q1, q2, q3, q4⟩ : Held2) = neg2 (commonTurn 0 1 ⟨p1, p2, p3, p4⟩) := by
    intro e1 e2 e3 e4
    apply Held2.ext <;> dsimp only [commonTurn, neg2] <;> linarith
  rcases mul_eq_zero.mp S1 with s1 | s1 <;> rcases mul_eq_zero.mp S2 with s2 | s2
  · obtain ⟨e1, e2⟩ := plus1 s1
    obtain ⟨e3, e4⟩ := plus2 s2
    exact Or.inl (left_of e1 e2 e3 e4)
  · obtain ⟨e1, e2⟩ := plus1 s1
    obtain ⟨e3, e4⟩ := minus2 s2
    have hRe' := hRe
    have hIm' := hIm
    rw [e1, e2, e3, e4] at hRe' hIm'
    have X : p1 * p3 + p2 * p4 = 0 := by linear_combination (-1 / 2) * hRe'
    have Y : p2 * p3 - p1 * p4 = 0 := by linear_combination (-1 / 2) * hIm'
    have Z : (p1 * p1 + p2 * p2) * (p3 * p3 + p4 * p4) = 0 := by
      linear_combination (p1 * p3 + p2 * p4) * X + (p2 * p3 - p1 * p4) * Y
    rcases mul_eq_zero.mp Z with z | z
    · obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp z
      exact Or.inr (right_of (by linarith) (by linarith) e3 e4)
    · obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp z
      exact Or.inl (left_of e1 e2 (by linarith) (by linarith))
  · obtain ⟨e1, e2⟩ := minus1 s1
    obtain ⟨e3, e4⟩ := plus2 s2
    have hRe' := hRe
    have hIm' := hIm
    rw [e1, e2, e3, e4] at hRe' hIm'
    have X : p1 * p3 + p2 * p4 = 0 := by linear_combination (-1 / 2) * hRe'
    have Y : p2 * p3 - p1 * p4 = 0 := by linear_combination (-1 / 2) * hIm'
    have Z : (p1 * p1 + p2 * p2) * (p3 * p3 + p4 * p4) = 0 := by
      linear_combination (p1 * p3 + p2 * p4) * X + (p2 * p3 - p1 * p4) * Y
    rcases mul_eq_zero.mp Z with z | z
    · obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp z
      exact Or.inl (left_of (by linarith) (by linarith) e3 e4)
    · obtain ⟨z1, z2⟩ := mul_self_add_mul_self_eq_zero.mp z
      exact Or.inr (right_of e1 e2 (by linarith) (by linarith))
  · obtain ⟨e1, e2⟩ := minus1 s1
    obtain ⟨e3, e4⟩ := minus2 s2
    exact Or.inr (right_of e1 e2 e3 e4)

theorem commonTurn_eq_add (c s : ℝ) (h : Held2) :
    commonTurn c s h = add2 (smul2 c h) (smul2 s (commonTurn 0 1 h)) := by
  apply Held2.ext <;> dsimp only [commonTurn, add2, smul2] <;> ring

theorem quarter_add (x y : Held2) :
    commonTurn 0 1 (add2 x y) = add2 (commonTurn 0 1 x) (commonTurn 0 1 y) := by
  apply Held2.ext <;> dsimp only [commonTurn, add2] <;> ring

theorem neg2_eq_smul (x : Held2) : neg2 x = smul2 (-1) x := by
  apply Held2.ext <;> dsimp only [neg2, smul2] <;> ring

theorem map_neg2 (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) (x : Held2) :
    T (neg2 x) = neg2 (T x) := by
  rw [neg2_eq_smul, hlin.2, ← neg2_eq_smul]

theorem unseen_pointwise (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hun : CommonTurnUnseenAfter T) (h : Held2) :
    T (commonTurn 0 1 h) = commonTurn 0 1 (T h) ∨
      T (commonTurn 0 1 h) = neg2 (commonTurn 0 1 (T h)) := by
  have q := records_of_plainAfterTurn_eq _ _ (hun 0 1 (by norm_num) h)
  have g := records_of_plainAfterTurn_eq _ _ (hun (3 / 5) (4 / 5) (by norm_num) h)
  rw [commonTurn_eq_add, hlin.1, hlin.2, hlin.2] at g
  exact pair_dichotomy (T h) (T (commonTurn 0 1 h)) q.1 q.2.1 q.2.2.1 q.2.2.2 g.1 g.2.1

theorem unseen_dichotomy (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hun : CommonTurnUnseenAfter T) : CommutesWithQuarter T ∨ AnticommutesWithQuarter T := by
  by_cases hc : CommutesWithQuarter T
  · exact Or.inl hc
  by_cases ha : AnticommutesWithQuarter T
  · exact Or.inr ha
  exfalso
  obtain ⟨h0, n0⟩ := not_forall.mp hc
  obtain ⟨h1, n1⟩ := not_forall.mp ha
  have a0 : T (commonTurn 0 1 h0) = neg2 (commonTurn 0 1 (T h0)) :=
    (unseen_pointwise T hlin hun h0).resolve_left n0
  have c1 : T (commonTurn 0 1 h1) = commonTurn 0 1 (T h1) :=
    (unseen_pointwise T hlin hun h1).resolve_right n1
  have lhs : T (commonTurn 0 1 (add2 h0 h1)) =
      add2 (neg2 (commonTurn 0 1 (T h0))) (commonTurn 0 1 (T h1)) := by
    rw [quarter_add, hlin.1, a0, c1]
  rcases unseen_pointwise T hlin hun (add2 h0 h1) with hp | hp
  · rw [lhs, hlin.1, quarter_add] at hp
    apply n0
    rw [a0]
    have k1 := congrArg Held2.a1 hp
    have k2 := congrArg Held2.a2 hp
    have k3 := congrArg Held2.b1 hp
    have k4 := congrArg Held2.b2 hp
    dsimp only [add2, neg2] at k1 k2 k3 k4
    apply Held2.ext <;> dsimp only [neg2] <;> linarith
  · rw [lhs, hlin.1, quarter_add] at hp
    apply n1
    rw [c1]
    have k1 := congrArg Held2.a1 hp
    have k2 := congrArg Held2.a2 hp
    have k3 := congrArg Held2.b1 hp
    have k4 := congrArg Held2.b2 hp
    dsimp only [add2, neg2] at k1 k2 k3 k4
    apply Held2.ext <;> dsimp only [neg2] <;> linarith

theorem unseen_of_commutes (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hc : CommutesWithQuarter T) : CommonTurnUnseenAfter T := by
  intro c s hcs h
  have e : T (commonTurn c s h) = commonTurn c s (T h) := by
    rw [commonTurn_eq_add, hlin.1, hlin.2, hlin.2, hc h, ← commonTurn_eq_add]
  rw [e, plainAfterTurn_commonTurn c s hcs]

theorem unseen_of_anticommutes (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (ha : AnticommutesWithQuarter T) : CommonTurnUnseenAfter T := by
  intro c s hcs h
  have e : T (commonTurn c s h) = commonTurn c (-s) (T h) := by
    rw [commonTurn_eq_add, hlin.1, hlin.2, hlin.2, ha h, commonTurn_eq_add c (-s)]
    apply Held2.ext <;> dsimp only [add2, smul2, neg2] <;> ring
  rw [e, plainAfterTurn_commonTurn c (-s) (by linear_combination hcs)]

theorem unseen_iff (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) :
    CommonTurnUnseenAfter T ↔ CommutesWithQuarter T ∨ AnticommutesWithQuarter T :=
  ⟨unseen_dichotomy T hlin, fun hca =>
    hca.elim (unseen_of_commutes T hlin) (unseen_of_anticommutes T hlin)⟩

theorem square_commutes_quarter (S : Held2 → Held2) (hlin : AdditiveHomogeneous S)
    (hun : CommonTurnUnseenAfter S) : CommutesWithQuarter (fun h => S (S h)) := by
  intro h
  rcases unseen_dichotomy S hlin hun with hc | ha
  · show S (S (commonTurn 0 1 h)) = commonTurn 0 1 (S (S h))
    rw [hc h, hc (S h)]
  · show S (S (commonTurn 0 1 h)) = commonTurn 0 1 (S (S h))
    rw [ha h, map_neg2 S hlin, ha (S h)]
    apply Held2.ext <;> dsimp only [neg2] <;> ring

theorem unseen_of_fixed_by_records (T : Held2 → Held2)
    (hfo : ∀ h h' : Held2, recA h = recA h' → recB h = recB h' → crossRe h = crossRe h' →
      crossIm h = crossIm h' →
      recA (T h) = recA (T h') ∧ recB (T h) = recB (T h') ∧ crossRe (T h) = crossRe (T h') ∧
        crossIm (T h) = crossIm (T h')) :
    CommonTurnUnseenAfter T := by
  intro c s hcs h
  obtain ⟨hA, hB, _, _⟩ := commonTurn_unseen c s hcs h
  obtain ⟨hRe, hIm⟩ := cross_invariant_under_commonTurn c s hcs h
  obtain ⟨kA, kB, kRe, kIm⟩ := hfo _ _ hA hB hRe hIm
  exact plainAfterTurn_eq_of_records _ _ kA kB kRe kIm

end APFPaper5.K3


theorem solution :
∀ (h h' : APFPaper5.K3.Held2)
  (hprof :
    @Eq.{1} ((x : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) → Prop)
      (APFPaper5.K3.plainAfterTurn h) (APFPaper5.K3.plainAfterTurn h')),
  And (@Eq.{1} Real (APFPaper5.K3.recA h) (APFPaper5.K3.recA h'))
    (And (@Eq.{1} Real (APFPaper5.K3.recB h) (APFPaper5.K3.recB h'))
      (And (@Eq.{1} Real (APFPaper5.K3.crossRe h) (APFPaper5.K3.crossRe h'))
        (@Eq.{1} Real (APFPaper5.K3.crossIm h) (APFPaper5.K3.crossIm h')))) := by
  exact @APFPaper5.K3.records_of_plainAfterTurn_eq
