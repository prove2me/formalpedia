-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ou_exponential_kernel_psd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:32:25.988598+00:00
-- url     : https://prove2.me/submissions/2ef29c63-311d-42ac-b625-444199b61253

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Matrix
open scoped BigOperators

private theorem applied_sde_exp_min
    (rate : ℝ) (hrate : 0 < rate) (s z : ℝ) :
    Real.exp (-rate * |s - z|) =
      Real.exp (-rate * s) *
        min (Real.exp (2 * rate * s)) (Real.exp (2 * rate * z)) *
          Real.exp (-rate * z) := by
  by_cases hij : s ≤ z
  · have hle : 2 * rate * s ≤ 2 * rate * z :=
      mul_le_mul_of_nonneg_left hij (by positivity)
    have hmin : min (Real.exp (2 * rate * s)) (Real.exp (2 * rate * z)) = Real.exp (2 * rate * s) := by
      exact min_eq_left (Real.exp_le_exp.mpr hle)
    calc
      Real.exp (-rate * |s - z|) =
          Real.exp ((-rate * s + 2 * rate * s) + -rate * z) := by
            congr 1
            rw [abs_of_nonpos (sub_nonpos.mpr hij)]
            ring
      _ = Real.exp (-rate * s) * Real.exp (2 * rate * s) *
            Real.exp (-rate * z) := by rw [Real.exp_add, Real.exp_add]
      _ = Real.exp (-rate * s) * min (Real.exp (2 * rate * s)) (Real.exp (2 * rate * z)) *
            Real.exp (-rate * z) := by simp [hmin]
  · have hji : z ≤ s := le_of_not_ge hij
    have hle : 2 * rate * z ≤ 2 * rate * s :=
      mul_le_mul_of_nonneg_left hji (by positivity)
    have hmin : min (Real.exp (2 * rate * s)) (Real.exp (2 * rate * z)) = Real.exp (2 * rate * z) := by
      exact min_eq_right (Real.exp_le_exp.mpr hle)
    calc
      Real.exp (-rate * |s - z|) =
          Real.exp ((-rate * s + 2 * rate * z) + -rate * z) := by
            congr 1
            rw [abs_of_nonneg (sub_nonneg.mpr hji)]
            ring
      _ = Real.exp (-rate * s) * Real.exp (2 * rate * z) *
            Real.exp (-rate * z) := by rw [Real.exp_add, Real.exp_add]
      _ = Real.exp (-rate * s) * min (Real.exp (2 * rate * s)) (Real.exp (2 * rate * z)) *
            Real.exp (-rate * z) := by simp [hmin]

theorem solution
    (n : ℕ) (rate V : ℝ) (hrate : 0 < rate) (hV : 0 ≤ V)
    (t : Fin n → ℝ) (a : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      a i * a j * (V * Real.exp (-rate * |t i - t j|)) := by
  let u : Fin n → ℝ := fun i => Real.exp (2 * rate * t i)
  let w : Fin n → ℝ := fun i => a i * Real.exp (-rate * t i)
  let sets : Fin n → Set ℝ := fun i => Set.Icc (0 : ℝ) (u i)
  have hmatrix :
      (Matrix.of fun i j : Fin n =>
        (volume : Measure ℝ).real (sets i ∩ sets j)).PosSemidef := by
    exact MeasureTheory.posSemidef_matrix_measure_inter
      (μ := (volume : Measure ℝ)) (s := sets)
      (fun _ => measurableSet_Icc)
      (fun i => isCompact_Icc.measure_ne_top)
  have hvol (i j : Fin n) :
      (volume : Measure ℝ).real (sets i ∩ sets j) = min (u i) (u j) := by
    dsimp [sets, u]
    simp [Set.Icc_inter_Icc, Real.exp_pos]
    exact ⟨(Real.exp_pos _).le, (Real.exp_pos _).le⟩
  have hquadratic :
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        w i * w j * min (u i) (u j) := by
    have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hmatrix w
    simpa [dotProduct, Matrix.mulVec, hvol, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hkernel (i j : Fin n) :
      Real.exp (-rate * |t i - t j|) =
        Real.exp (-rate * t i) * min (u i) (u j) *
          Real.exp (-rate * t j) := by
    simpa only [u] using applied_sde_exp_min rate hrate (t i) (t j)
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (V * Real.exp (-rate * |t i - t j|))) =
        V * (∑ i : Fin n, ∑ j : Fin n,
          w i * w j * min (u i) (u j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [w]
    rw [hkernel i j]
    ring
  rw [hsum]
  exact mul_nonneg hV hquadratic
