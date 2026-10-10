-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonAggregatePMF_panjer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T23:18:26.045106+00:00
-- url     : https://prove2.me/submissions/ac186879-9c7b-4cac-a83d-b8fd1bf9589c

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonPanjerStep
import Definitions.Def_actuarial_compoundPoissonSeverityPower
import Definitions.Def_actuarial_compoundPoissonConvolution
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_aggregateConvolution
import Theorems.Thm_ActuarialValuation_aggregateConvolution_comm
import Theorems.Thm_ActuarialValuation_aggregateConvolution_assoc
import Theorems.Thm_ActuarialValuation_aggregateConvolution_delta_right
import Theorems.Thm_ActuarialValuation_compoundPoissonCountWeight_ratio
import Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_one
import Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_outside
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
private theorem p27_comm (f g : ℕ → ℝ) (s : ℕ) : compoundPoissonConvolution f g s = compoundPoissonConvolution g f s := by
  change aggregateConvolution f g s = aggregateConvolution g f s
  exact aggregateConvolution_comm f g s
private theorem p27_assoc (f g h : ℕ → ℝ) (s : ℕ) : compoundPoissonConvolution (compoundPoissonConvolution f g) h s = compoundPoissonConvolution f (compoundPoissonConvolution g h) s := by
  change aggregateConvolution (aggregateConvolution f g) h s = aggregateConvolution f (aggregateConvolution g h) s
  exact aggregateConvolution_assoc f g h s
private theorem p27_right (f : ℕ → ℝ) (s : ℕ) : compoundPoissonConvolution f (fun j => if j = 0 then 1 else 0) s = f s := by
  change aggregateConvolution f (fun j => if j = 0 then 1 else 0) s = f s
  exact aggregateConvolution_delta_right f s
private theorem p27_weighted (f g : ℕ → ℝ) (s : ℕ) : (s : ℝ) * compoundPoissonConvolution f g s = compoundPoissonConvolution (fun j => (j : ℝ) * f j) g s + compoundPoissonConvolution f (fun j => (j : ℝ) * g j) s := by
  unfold compoundPoissonConvolution
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
  have hn : j + (s - j) = s := by omega
  have hr : (s : ℝ) = (j : ℝ) + ((s - j : ℕ) : ℝ) := by exact_mod_cast hn.symm
  rw [hr] <;> ring
private theorem p27_scale (c : ℝ) (f g : ℕ → ℝ) (s : ℕ) : compoundPoissonConvolution f (fun k => c * g k) s = c * compoundPoissonConvolution f g s := by
  unfold compoundPoissonConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  ring
private theorem p27_weighted_power (f : ℕ → ℝ) (m s : ℕ) : (s : ℝ) * compoundPoissonSeverityPower f (m + 1) s = ((m + 1 : ℕ) : ℝ) * compoundPoissonConvolution
        (fun j => (j : ℝ) * f j) (compoundPoissonSeverityPower f m) s := by
  induction m generalizing s with
  | zero =>
      rw [compoundPoissonSeverityPower_one]
      simp only [Nat.zero_add, Nat.cast_one, one_mul]
      change (s : ℝ) * f s = compoundPoissonConvolution (fun j => (j : ℝ) * f j)
          (fun j => if j = 0 then 1 else 0) s
      rw [p27_right]
  | succ m ih =>
      let F : ℕ → ℝ := fun j => (j : ℝ) * f j
      let P : ℕ → ℝ := compoundPoissonSeverityPower f (m + 1)
      let Q : ℕ → ℝ := compoundPoissonSeverityPower f m
      have hP : P = compoundPoissonConvolution f Q := rfl
      change (s : ℝ) * compoundPoissonConvolution f P s = (((m + 1) + 1 : ℕ) : ℝ) * compoundPoissonConvolution F P s
      rw [p27_weighted]
      have hfun : (fun (k : ℕ) => (k : ℝ) * P k) = (fun (k : ℕ) => (((m + 1 : ℕ) : ℝ) * compoundPoissonConvolution F Q k)) := by
        funext k; exact ih k
      rw [hfun, p27_scale]
      have hswap : compoundPoissonConvolution f (compoundPoissonConvolution F Q) s = compoundPoissonConvolution F P s := by
        have hcomm : compoundPoissonConvolution f F = compoundPoissonConvolution F f := by funext k; exact p27_comm f F k
        rw [hP, ← p27_assoc f F Q, hcomm, p27_assoc F f Q]
      rw [hswap]
      push_cast <;> ring
theorem solution (rate : ℝ) (f : ℕ → ℝ) (s : ℕ) (hf0 : f 0 = 0) : compoundPoissonAggregatePMF rate f (s + 1) = compoundPoissonPanjerStep rate f
        (compoundPoissonAggregatePMF rate f) (s + 1) := by
  let t : ℕ := s + 1
  let F : ℕ → ℝ := fun j => (j : ℝ) * f j
  let W : ℕ → ℝ := compoundPoissonCountWeight rate
  let C : ℕ → ℕ → ℝ := compoundPoissonSeverityPower f
  let G : ℕ → ℝ := compoundPoissonAggregatePMF rate f
  have htne : (t : ℝ) ≠ 0 := by positivity
  have hz : C 0 t = 0 := by simp [C, compoundPoissonSeverityPower, show t ≠ 0 by omega]
  have hinner (j : ℕ) (hj : 0 < j) (hjle : j ≤ t) : (∑ m ∈ Finset.range (s + 1), W m * C m (t - j)) = G (t - j) := by
    have hn : s + 1 = (t - j + 1) + (j - 1) := by omega
    have htail : (∑ m ∈ Finset.range (j - 1), W (t - j + 1 + m) * C (t - j + 1 + m) (t - j)) = 0 := by
      apply Finset.sum_eq_zero; intro m hm
      change W (t - j + 1 + m) *
        compoundPoissonSeverityPower f (t - j + 1 + m) (t - j) = 0
      rw [compoundPoissonSeverityPower_outside f (t - j + 1 + m) (t - j) hf0 (by omega), mul_zero]
    calc
      (∑ m ∈ Finset.range (s + 1), W m * C m (t - j)) = (∑ m ∈ Finset.range (t - j + 1), W m * C m (t - j)) + (∑ m ∈ Finset.range (j - 1), W (t - j + 1 + m) * C (t - j + 1 + m) (t - j)) := by
            nth_rw 1 [hn]
            rw [Finset.sum_range_add]
      _ = G (t - j) := by
            rw [htail, add_zero] <;> rfl
  have hswap : (∑ m ∈ Finset.range (s + 1), W m * compoundPoissonConvolution F (C m) t) = ∑ j ∈ Finset.range (t + 1), F j * G (t - j) := by
    calc
      (∑ m ∈ Finset.range (s + 1), W m * compoundPoissonConvolution F (C m) t) = ∑ m ∈ Finset.range (s + 1),
          ∑ j ∈ Finset.range (t + 1), W m * (F j * C m (t - j)) := by
            apply Finset.sum_congr rfl; intro m hm
            unfold compoundPoissonConvolution
            rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (t + 1), ∑ m ∈ Finset.range (s + 1), W m * (F j * C m (t - j)) :=
            Finset.sum_comm
      _ = ∑ j ∈ Finset.range (t + 1), F j * (∑ m ∈ Finset.range (s + 1), W m * C m (t - j)) := by
            apply Finset.sum_congr rfl; intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m hm
            ring
      _ = ∑ j ∈ Finset.range (t + 1), F j * G (t - j) := by
            apply Finset.sum_congr rfl; intro j hj
            by_cases hj0 : j = 0
            · subst j
              simp [F]
            · have hjle : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rw [hinner j (by omega) hjle]
  have hscaled : (t : ℝ) * G t = rate * (∑ j ∈ Finset.range (t + 1), F j * G (t - j)) := by
    calc
      (t : ℝ) * G t = ∑ m ∈ Finset.range (t + 1), W m * ((t : ℝ) * C m t) := by
          unfold G compoundPoissonAggregatePMF
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m hm
          ring
      _ = ∑ m ∈ Finset.range (s + 1), W (m + 1) * ((t : ℝ) * C (m + 1) t) := by
            have hn : t + 1 = 1 + (s + 1) := by omega
            nth_rw 1 [hn]
            rw [Finset.sum_range_add]
            simp only [Finset.sum_range_one, hz, mul_zero, zero_add]
            all_goals simp only [Nat.add_comm]
      _ = ∑ m ∈ Finset.range (s + 1), (rate * W m) * compoundPoissonConvolution F (C m) t := by
            apply Finset.sum_congr rfl; intro m hm
            rw [p27_weighted_power f m t]
            let X : ℝ := compoundPoissonConvolution F (C m) t
            have hw : (((m + 1 : ℕ) : ℝ) * W (m + 1)) = rate * W m := by
              simpa only [Nat.cast_add, Nat.cast_one] using (compoundPoissonCountWeight_ratio rate m)
            change W (m + 1) * (((m + 1 : ℕ) : ℝ) * X) = (rate * W m) * X
            calc
              W (m + 1) * (((m + 1 : ℕ) : ℝ) * X) = ((((m + 1 : ℕ) : ℝ) * W (m + 1)) * X) := by ring
              _ = (rate * W m) * X := by rw [hw]
      _ = rate * (∑ m ∈ Finset.range (s + 1), W m * compoundPoissonConvolution F (C m) t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m hm
            ring
      _ = rate * (∑ j ∈ Finset.range (t + 1), F j * G (t - j)) := by
            rw [hswap]
  change G t = rate / (t : ℝ) * (∑ j ∈ Finset.range (t + 1), (j : ℝ) * f j * G (t - j))
  calc
    G t = ((t : ℝ) * G t) / (t : ℝ) := by
      field_simp [htne]
    _ = (rate * (∑ j ∈ Finset.range (t + 1), F j * G (t - j))) / (t : ℝ) := by rw [hscaled]
    _ = rate / (t : ℝ) * (∑ j ∈ Finset.range (t + 1), (j : ℝ) * f j * G (t - j)) := by
          dsimp [F]
          ring
