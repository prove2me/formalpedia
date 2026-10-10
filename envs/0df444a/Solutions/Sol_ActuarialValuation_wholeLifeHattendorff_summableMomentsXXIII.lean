-- Prove2me | solution 1 for ActuarialValuation.wholeLifeHattendorff_summableMomentsXXIII
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:48:43.592978+00:00
-- url     : https://prove2.me/submissions/447803cd-fe95-4804-aa70-6ba50c07e823

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
    (w rho : ℕ → ℝ) (hw : Summable w)
    (hNonneg : ∀ k, 0 ≤ w k)
    (hTotal : (∑' k : ℕ, w k) = 1)
    (hS : ∀ t, 0 < wholeLifeTailMass w t)
    (hVar : Summable (fun t : ℕ =>
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)))
    (hPrefix : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
        w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
      (∑ t ∈ Finset.range N,
        (rho t) ^ 2 * w t *
          (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t)) -
      wholeLifeTailMass w N *
        (-(∑ t ∈ Finset.range N,
          rho t * (w t / wholeLifeTailMass w t))) ^ 2) :
  Summable (fun k : ℕ => w k * wholeLifeCompleteInnovation w rho k) ∧
  Summable (fun k : ℕ =>
    w k * (wholeLifeCompleteInnovation w rho k) ^ 2) := by
  classical
  let S (t : ℕ) : ℝ := wholeLifeTailMass w t
  let A (n : ℕ) : ℝ :=
    -(∑ t ∈ Finset.range n, rho t * (w t / S t))
  let a (t : ℕ) : ℝ := (rho t) ^ 2 * w t * (S (t + 1) / S t)
  have ha : Summable a := hVar
  have hanonneg (t : ℕ) : 0 ≤ a t := by
    dsimp [a, S]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hNonneg t))
      (div_nonneg (le_of_lt (hS (t + 1))) (le_of_lt (hS t)))
  have hpartialA (n : ℕ) :
      (∑ t ∈ Finset.range n, a t) ≤ ∑' t : ℕ, a t := by
    exact ha.sum_le_tsum (Finset.range n)
      (by intro t ht; exact hanonneg t)
  have hpartialW (n : ℕ) :
      (∑ k ∈ Finset.range n, w k) ≤ 1 := by
    have hb := hw.sum_le_tsum (Finset.range n)
      (by intro k hk; exact hNonneg k)
    simpa only [hTotal] using hb
  have hSQnonneg (k : ℕ) :
      0 ≤ w k * (wholeLifeCompleteInnovation w rho k) ^ 2 :=
    mul_nonneg (hNonneg k) (sq_nonneg _)
  have hPref (n : ℕ) :
      (∑ k ∈ Finset.range n,
        w k * (wholeLifeCompleteInnovation w rho k) ^ 2) =
          (∑ t ∈ Finset.range n, a t) - S n * (A n) ^ 2 := by
    exact hPrefix n
  have hSQprefix (n : ℕ) :
      (∑ k ∈ Finset.range n,
        w k * (wholeLifeCompleteInnovation w rho k) ^ 2) ≤
          ∑' t : ℕ, a t := by
    rw [hPref n]
    have hprod : 0 ≤ S n * (A n) ^ 2 :=
      mul_nonneg (le_of_lt (hS n)) (sq_nonneg _)
    linarith [hpartialA n]
  have hSQsummable :
      Summable (fun k : ℕ =>
        w k * (wholeLifeCompleteInnovation w rho k) ^ 2) :=
    summable_of_sum_range_le hSQnonneg hSQprefix
  have hABSbounds (n : ℕ) :
      (∑ k ∈ Finset.range n,
        |w k * wholeLifeCompleteInnovation w rho k|) ^ 2 ≤
          ∑' t : ℕ, a t := by
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
      (r := fun k => |w k * wholeLifeCompleteInnovation w rho k|)
      (f := fun k => w k)
      (g := fun k => w k * (wholeLifeCompleteInnovation w rho k) ^ 2)
      (by intro k hk; exact hNonneg k)
      (by intro k hk; exact hSQnonneg k)
      (by intro k hk
          apply le_of_eq
          rw [sq_abs]
          ring)
    have hSqprefixNonneg :
        0 ≤ ∑ k ∈ Finset.range n,
          w k * (wholeLifeCompleteInnovation w rho k) ^ 2 :=
      Finset.sum_nonneg (by intro k hk; exact hSQnonneg k)
    calc
      _ ≤ (∑ k ∈ Finset.range n, w k) *
          (∑ k ∈ Finset.range n,
            w k * (wholeLifeCompleteInnovation w rho k) ^ 2) := hCS
      _ ≤ (1 : ℝ) * (∑ k ∈ Finset.range n,
            w k * (wholeLifeCompleteInnovation w rho k) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (hpartialW n) hSqprefixNonneg
      _ ≤ ∑' t : ℕ, a t := by simpa using hSQprefix n
  have hABSsummable : Summable (fun k : ℕ =>
      |w k * wholeLifeCompleteInnovation w rho k|) := by
    apply (summable_of_sum_range_le
      (c := ((∑' t : ℕ, a t) + 1) / 2)
      (fun k => abs_nonneg _) ?_)
    intro n
    let x : ℝ := ∑ k ∈ Finset.range n,
        |w k * wholeLifeCompleteInnovation w rho k|
    have hbound := hABSbounds n
    have hsq : x ^ 2 ≤ ∑' t : ℕ, a t := hbound
    nlinarith [sq_nonneg (x - 1)]
  have hMEANsummable : Summable (fun k : ℕ =>
      w k * wholeLifeCompleteInnovation w rho k) :=
    (summable_norm_iff).mp (by
      simpa only [Real.norm_eq_abs] using hABSsummable)
  exact ⟨hMEANsummable, hSQsummable⟩

