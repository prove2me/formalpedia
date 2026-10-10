-- Prove2me | solution 1 for ActuarialValuation.discountedAnnualGain_variance_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:04:24.081043+00:00
-- url     : https://prove2.me/submissions/1877af5e-5303-49f3-bf32-cab2a6530b3d

import Mathlib
import Definitions.Def_actuarial_discountedAnnualGainSum
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioVariance
import Theorems.Thm_ActuarialValuation_finiteScenarioExpectation_linear
import Theorems.Thm_ActuarialValuation_finiteScenarioCovariance_symm
import Theorems.Thm_ActuarialValuation_finiteScenarioVariance_pair_add
import Theorems.Thm_ActuarialValuation_finiteScenarioVariance_scale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

private theorem p2m_cov_add_left {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X Y Z : Ω → ℝ) :
    finiteScenarioCovariance w (fun ω => X ω + Y ω) Z =
      finiteScenarioCovariance w X Z + finiteScenarioCovariance w Y Z := by
  have hμ : finiteScenarioExpectation w (fun ω => X ω + Y ω) =
      finiteScenarioExpectation w X + finiteScenarioExpectation w Y := by
    simpa using finiteScenarioExpectation_linear w X Y 1
  unfold finiteScenarioCovariance
  rw [hμ]
  calc
    (∑ ω : Ω, w ω *
      ((X ω + Y ω) -
        (finiteScenarioExpectation w X + finiteScenarioExpectation w Y)) *
       (Z ω - finiteScenarioExpectation w Z)) =
      ∑ ω : Ω, (w ω * (X ω - finiteScenarioExpectation w X) *
          (Z ω - finiteScenarioExpectation w Z) +
        w ω * (Y ω - finiteScenarioExpectation w Y) *
          (Z ω - finiteScenarioExpectation w Z)) := by
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = _ := by rw [Finset.sum_add_distrib]

private theorem p2m_cov_scale_left {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X Y : Ω → ℝ) (a : ℝ) :
    finiteScenarioCovariance w (fun ω => a * X ω) Y =
      a * finiteScenarioCovariance w X Y := by
  have hμ : finiteScenarioExpectation w (fun ω => a * X ω) =
      a * finiteScenarioExpectation w X := by
    unfold finiteScenarioExpectation
    calc
      (∑ ω : Ω, w ω * (a * X ω)) =
        ∑ ω : Ω, a * (w ω * X ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
      _ = _ := by rw [Finset.mul_sum]
  unfold finiteScenarioCovariance
  rw [hμ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

private theorem p2m_cov_scale_right {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (X Y : Ω → ℝ) (a : ℝ) :
    finiteScenarioCovariance w X (fun ω => a * Y ω) =
      a * finiteScenarioCovariance w X Y := by
  calc
    _ = finiteScenarioCovariance w (fun ω => a * Y ω) X :=
      finiteScenarioCovariance_symm w X (fun ω => a * Y ω)
    _ = a * finiteScenarioCovariance w Y X :=
      p2m_cov_scale_left w Y X a
    _ = _ := by rw [finiteScenarioCovariance_symm w Y X]

private theorem p2m_cov_prefix_zero {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (G : ℕ → Ω → ℝ) (v : ℝ) (n : ℕ)
    (Y : Ω → ℝ)
    (hz : ∀ i ∈ Finset.range n,
      finiteScenarioCovariance w (G i) Y = 0) :
    finiteScenarioCovariance w (discountedAnnualGainSum G v n) Y = 0 := by
  induction n with
  | zero =>
      simp [discountedAnnualGainSum, finiteScenarioCovariance,
        finiteScenarioExpectation]
  | succ n ih =>
      have hp : ∀ i ∈ Finset.range n,
          finiteScenarioCovariance w (G i) Y = 0 := by
        intro i hi
        exact hz i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
      have hn : finiteScenarioCovariance w (G n) Y = 0 :=
        hz n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have heq : (fun ω => discountedAnnualGainSum G v (n + 1) ω) =
          (fun ω => discountedAnnualGainSum G v n ω + v ^ n * G n ω) := by
        funext ω
        simp [discountedAnnualGainSum, Finset.sum_range_succ]
      change finiteScenarioCovariance w
        (fun ω => discountedAnnualGainSum G v (n + 1) ω) Y = 0
      rw [heq, p2m_cov_add_left, p2m_cov_scale_left,
        ih hp, hn]
      ring

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (G : ℕ → Ω → ℝ) (v : ℝ) (n : ℕ)
    (horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → finiteScenarioCovariance w (G i) (G j) = 0) :
    finiteScenarioVariance w (discountedAnnualGainSum G v n) =
      ∑ k ∈ Finset.range n, v ^ (2 * k) * finiteScenarioVariance w (G k) := by
  induction n with
  | zero =>
      simp [discountedAnnualGainSum, finiteScenarioVariance,
        finiteScenarioExpectation]
  | succ n ih =>
      have hsmall : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
          i ≠ j → finiteScenarioCovariance w (G i) (G j) = 0 := by
        intro i hi j hj hne
        exact horth i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
          j (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))) hne
      have hcross : finiteScenarioCovariance w
          (discountedAnnualGainSum G v n) (G n) = 0 := by
        apply p2m_cov_prefix_zero w G v n (G n)
        intro i hi
        exact horth i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
          n (Finset.mem_range.mpr (Nat.lt_succ_self n))
          (by have hlt := Finset.mem_range.mp hi; omega)
      have hcrossScaled : finiteScenarioCovariance w
          (discountedAnnualGainSum G v n) (fun ω => v ^ n * G n ω) = 0 := by
        rw [p2m_cov_scale_right, hcross]
        ring
      have heq : (fun ω => discountedAnnualGainSum G v (n + 1) ω) =
          (fun ω => discountedAnnualGainSum G v n ω + v ^ n * G n ω) := by
        funext ω
        simp [discountedAnnualGainSum, Finset.sum_range_succ]
      change finiteScenarioVariance w
        (fun ω => discountedAnnualGainSum G v (n + 1) ω) =
          ∑ k ∈ Finset.range (n + 1),
            v ^ (2 * k) * finiteScenarioVariance w (G k)
      rw [heq, finiteScenarioVariance_pair_add w
        (discountedAnnualGainSum G v n) (fun ω => v ^ n * G n ω) hcrossScaled]
      rw [ih hsmall, finiteScenarioVariance_scale]
      have hp : (v ^ n) ^ 2 = v ^ (2 * n) := by
        rw [← pow_mul, mul_comm n 2]
      rw [hp, Finset.sum_range_succ]
