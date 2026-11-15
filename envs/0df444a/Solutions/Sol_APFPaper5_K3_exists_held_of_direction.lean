-- Prove2me | solution 1 for APFPaper5.K3.exists_held_of_direction
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:37:15.875684+00:00
-- url     : https://prove2.me/submissions/5a8591e5-8dd3-4e8c-a701-56799b692820

import Theorems.Thm_APFPaper5_K3_cross_invariant_under_commonTurn
import Theorems.Thm_APFPaper5_K3_relativeTurn_keeps_own_records
import Theorems.Thm_APFPaper5_K3_relativeTurn_rotates_cross
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_marks_of_the_carrier
title: The physical objects of the carrier are the three-direction mark space: same numbers, turns are its rotations, the rate flip is its mirror
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_MarkOfHeld.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model. The last statement carries hroot.
statement: (mark_length) the length of the direction of a held state is its total cost.
 (mark_commonTurn, overlap_commonTurn_left) a common turn changes neither the direction nor the number.
 (number_between) twice the number between two held states is the product of their costs plus the product
 of their directions. For unit cost this is (1 + x) / 2, the score of Thm_APFPaper5_K1_rank_three.
 (mark_exclusive) the two components alone have opposite directions and number zero.
 (mark_relativeTurn) a turn of one component rotates the direction about the third axis.
 (mark_mix) a recombination rotates it about the second axis, by twice the angle.
 (mark_rateFlip) the rate flip reverses the second coordinate: a mirror.
 (same_object_iff_same_mark) two held states are the same physical object exactly when they have the same
 total cost and the same direction.
 (exists_held_of_direction) every direction is the direction of a held state.
reading: the carrier is the space of amplitudes over the mark space in which the earlier passes placed the
 marks. Its maps built from turns and recombinations act there as rotations; the rate flip acts as a mirror.
not_claimed: that the marks at an interface fill three directions; that the carrier is the only space of
 amplitudes over them; any K.
-/
import Definitions.Def_APFPaper5_K3_MarkOfHeld
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K3

theorem mark_length (h : Held2) :
    dot3 (markDirection h) (markDirection h) = totalCost h * totalCost h := by
  dsimp only [dot3, markDirection, totalCost, crossRe, crossIm, recA, recB]
  ring

theorem mark_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    markDirection (commonTurn c s h) = markDirection h := by
  obtain ⟨hA, hB, _, _⟩ := commonTurn_unseen c s hcs h
  obtain ⟨hRe, hIm⟩ := cross_invariant_under_commonTurn c s hcs h
  dsimp only [markDirection]
  rw [hA, hB, hRe, hIm]

theorem overlap_commonTurn_left (c s : ℝ) (hcs : c * c + s * s = 1) (h k : Held2) :
    overlap (commonTurn c s h) k = overlap h k := by
  have e : overlap (commonTurn c s h) k = (c * c + s * s) * overlap h k := by
    dsimp only [overlap, commonTurn]
    ring
  rw [e, hcs, one_mul]

theorem number_between (h k : Held2) :
    2 * overlap h k = totalCost h * totalCost k + dot3 (markDirection h) (markDirection k) := by
  dsimp only [overlap, dot3, markDirection, totalCost, crossRe, crossIm, recA, recB]
  ring

theorem mark_exclusive :
    markDirection ⟨1, 0, 0, 0⟩ = ⟨0, 0, 1⟩ ∧ markDirection ⟨0, 0, 1, 0⟩ = ⟨0, 0, -1⟩ ∧
      overlap ⟨1, 0, 0, 0⟩ ⟨0, 0, 1, 0⟩ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply V3.ext <;> dsimp only [markDirection, crossRe, crossIm, recA, recB] <;> norm_num
  · apply V3.ext <;> dsimp only [markDirection, crossRe, crossIm, recA, recB] <;> norm_num
  · dsimp only [overlap]
    norm_num

theorem mark_relativeTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    markDirection (relativeTurn c s h) =
      ⟨c * (markDirection h).x + s * (markDirection h).y,
        c * (markDirection h).y - s * (markDirection h).x, (markDirection h).z⟩ := by
  obtain ⟨hA, hB⟩ := relativeTurn_keeps_own_records c s hcs h
  obtain ⟨hRe, hIm⟩ := relativeTurn_rotates_cross c s h
  apply V3.ext
  · dsimp only [markDirection]
    rw [hRe]
    ring
  · dsimp only [markDirection]
    rw [hIm]
    ring
  · dsimp only [markDirection]
    rw [hA, hB]

theorem mark_mix (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    markDirection (mix c s h) =
      ⟨(c * c - s * s) * (markDirection h).x + 2 * c * s * (markDirection h).z,
        (markDirection h).y,
        (c * c - s * s) * (markDirection h).z - 2 * c * s * (markDirection h).x⟩ := by
  apply V3.ext
  · dsimp only [markDirection, mix, crossRe, crossIm, recA, recB]
    ring
  · dsimp only [markDirection, mix, crossRe, crossIm, recA, recB]
    linear_combination (2 * (h.a2 * h.b1 - h.a1 * h.b2)) * hcs
  · dsimp only [markDirection, mix, crossRe, crossIm, recA, recB]
    ring

theorem mark_rateFlip (h : Held2) :
    markDirection (rateFlip h) =
      ⟨(markDirection h).x, -(markDirection h).y, (markDirection h).z⟩ := by
  apply V3.ext <;> dsimp only [markDirection, rateFlip, crossRe, crossIm, recA, recB] <;> ring

theorem same_object_iff_same_mark (h k : Held2) :
    plainAfterTurn h = plainAfterTurn k ↔
      totalCost h = totalCost k ∧ markDirection h = markDirection k := by
  rw [plainAfterTurn_eq_iff_records]
  constructor
  · rintro ⟨hA, hB, hRe, hIm⟩
    refine ⟨?_, ?_⟩
    · dsimp only [totalCost]
      rw [hA, hB]
    · dsimp only [markDirection]
      rw [hA, hB, hRe, hIm]
  · rintro ⟨hN, hM⟩
    have mx := congrArg V3.x hM
    have my := congrArg V3.y hM
    have mz := congrArg V3.z hM
    dsimp only [markDirection] at mx my mz
    dsimp only [totalCost] at hN
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_held_of_direction (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (v : V3) :
    ∃ h : Held2, markDirection h = v ∧ totalCost h * totalCost h = dot3 v v := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨N, hN0, hN⟩ := hroot (dot3 ⟨x, y, z⟩ ⟨x, y, z⟩)
    (add_nonneg (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)) (mul_self_nonneg z))
  dsimp only [dot3] at hN ⊢
  have hNz : 0 ≤ N + z := by
    by_contra hneg
    have h1 : 0 < -z - N := by linarith
    have h2 : 0 < N - z := by linarith
    nlinarith [mul_pos h1 h2, mul_self_nonneg x, mul_self_nonneg y]
  obtain ⟨r, _, hr⟩ := hroot ((N + z) / 2) (by linarith)
  by_cases hz : r = 0
  · have hNz0 : N + z = 0 := by rw [hz] at hr; linarith
    have hxy : x * x + y * y = 0 := by
      have hzN : z = -N := by linarith
      rw [hzN] at hN
      linarith
    obtain ⟨hx, hy⟩ := mul_self_add_mul_self_eq_zero.mp hxy
    obtain ⟨t, _, ht⟩ := hroot N hN0
    refine ⟨⟨0, 0, t, 0⟩, ?_, ?_⟩
    · apply V3.ext
      · dsimp only [markDirection, crossRe]
        rw [hx]
        ring
      · dsimp only [markDirection, crossIm]
        rw [hy]
        ring
      · dsimp only [markDirection, recA, recB]
        linarith
    · dsimp only [totalCost, recA, recB]
      have e : (0 : ℝ) * 0 + 0 * 0 + (t * t + 0 * 0) = N := by linarith
      rw [e]
      linarith
  · have h2r : (2 * r) ≠ 0 := mul_ne_zero two_ne_zero hz
    have hb1 : 2 * r * (x / (2 * r)) = x := by field_simp
    have hb2 : 2 * r * (-(y / (2 * r))) = -y := by field_simp
    have h4 : 4 * (r * r) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hz hz)
    have hZ : r * r + 0 * 0 - (x / (2 * r) * (x / (2 * r)) + -(y / (2 * r)) * -(y / (2 * r))) = z := by
      apply mul_left_cancel₀ h4
      linear_combination (4 * (r * r + (N + z) / 2) - 4 * z) * hr -
        (2 * r * (x / (2 * r)) + x) * hb1 - (2 * r * (-(y / (2 * r))) - y) * hb2 + hN
    refine ⟨⟨r, 0, x / (2 * r), -(y / (2 * r))⟩, ?_, ?_⟩
    · apply V3.ext
      · dsimp only [markDirection, crossRe]
        linear_combination hb1
      · dsimp only [markDirection, crossIm]
        linear_combination -hb2
      · dsimp only [markDirection, recA, recB]
        exact hZ
    · dsimp only [totalCost, recA, recB]
      have e : r * r + 0 * 0 + (x / (2 * r) * (x / (2 * r)) + -(y / (2 * r)) * -(y / (2 * r))) = N := by
        linear_combination 2 * hr - hZ
      rw [e]
      linarith

end APFPaper5.K3


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
            (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t))
  (v : APFPaper5.K3.V3),
  @Exists.{1} APFPaper5.K3.Held2 fun (h : APFPaper5.K3.Held2) =>
    And (@Eq.{1} APFPaper5.K3.V3 (APFPaper5.K3.markDirection h) v)
      (@Eq.{1} Real
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K3.totalCost h)
          (APFPaper5.K3.totalCost h))
        (APFPaper5.K3.dot3 v v)) := by
  exact @APFPaper5.K3.exists_held_of_direction
