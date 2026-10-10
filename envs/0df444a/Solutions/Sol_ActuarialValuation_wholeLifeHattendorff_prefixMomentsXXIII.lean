-- Prove2me | solution 1 for ActuarialValuation.wholeLifeHattendorff_prefixMomentsXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T23:22:29.088185+00:00
-- url     : https://prove2.me/submissions/f4f7a6bc-17aa-47ce-a244-dbcf41338d91

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass
import Theorems.Thm_ActuarialValuation_wholeLifeTailMass_succ_helperXXIII
import Theorems.Thm_ActuarialValuation_wholeLifeCompleteInnovation_pathwiseXXIII

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (w rho : ℕ → ℝ) (hw : Summable w)
    (hS : ∀ t, 0 < wholeLifeTailMass w t) (N : ℕ) :
  (∑ k ∈ Finset.range N, w k * wholeLifeCompleteInnovation w rho k) =
    -(wholeLifeTailMass w N *
      (-(∑ t ∈ Finset.range N,
        rho t * (w t / wholeLifeTailMass w t)))) ∧
  (∑ k ∈ Finset.range N,
      w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
    (∑ t ∈ Finset.range N,
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)) -
      wholeLifeTailMass w N *
        (-(∑ t ∈ Finset.range N,
          rho t * (w t / wholeLifeTailMass w t))) ^ 2 := by
  let S (t : ℕ) : ℝ := wholeLifeTailMass w t
  let A (n : ℕ) : ℝ :=
    -(∑ t ∈ Finset.range n, rho t * (w t / S t))
  let a (t : ℕ) : ℝ := (rho t) ^ 2 * w t * (S (t + 1) / S t)
  have hSsucc (t : ℕ) : S t = w t + S (t + 1) := by
    simpa only [S] using wholeLifeTailMass_succ_helperXXIII w t hw
  have hAsucc (n : ℕ) :
      A (n + 1) = A n - rho n * (w n / S n) := by
    dsimp [A]
    rw [Finset.sum_range_succ]
    ring
  have hA0 : A 0 = 0 := by simp [A]
  have hpath (k : ℕ) :
      wholeLifeCompleteInnovation w rho k =
        A k + rho k * (S (k + 1) / S k) := by
    rw [wholeLifeCompleteInnovation_pathwiseXXIII]
    dsimp [A, S]
    have hk : wholeLifeTailMass w (k + 1) =
        wholeLifeTailMass w k - w k := by
      linarith [hSsucc k]
    rw [hk]
    field_simp [ne_of_gt (hS k)]
  have hfirststep (k : ℕ) :
      w k * wholeLifeCompleteInnovation w rho k =
      S k * A k - S (k + 1) * A (k + 1) := by
    rw [hpath k, hAsucc k]
    have hk : S (k + 1) = S k - w k := by
      linarith [hSsucc k]
    rw [hk]
    have hnz : S k ≠ 0 := ne_of_gt (hS k)
    field_simp [hnz]
    ring
  have hsecondstep (k : ℕ) :
      w k * (wholeLifeCompleteInnovation w rho k) ^ 2 =
        S k * (A k) ^ 2 - S (k + 1) * (A (k + 1)) ^ 2 + a k := by
    rw [hpath k, hAsucc k]
    dsimp [a]
    have hk : S (k + 1) = S k - w k := by
      linarith [hSsucc k]
    rw [hk]
    have hnz : S k ≠ 0 := ne_of_gt (hS k)
    field_simp [hnz]
    ring
  have hmeanprefix (N : ℕ) :
      (∑ k ∈ Finset.range N, w k * wholeLifeCompleteInnovation w rho k) =
        -(S N * A N) := by
    induction N with
    | zero => simp [hA0]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hfirststep]
      ring
  have hvarprefix (N : ℕ) :
      (∑ k ∈ Finset.range N, w k *
        (wholeLifeCompleteInnovation w rho k) ^ 2) =
        (∑ t ∈ Finset.range N, a t) - S N * (A N) ^ 2 := by
    induction N with
    | zero => simp [hA0]
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hsecondstep]
      ring
  constructor
  · simpa only [S, A] using hmeanprefix N
  · simpa only [S, A, a] using hvarprefix N

