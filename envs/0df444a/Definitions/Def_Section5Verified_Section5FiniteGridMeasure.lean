-- Prove2me | Definitions.Def_Section5Verified_Section5FiniteGridMeasure
-- name    : Section5Verified_Section5FiniteGridMeasure
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:16:50.809278+00:00
-- url     : https://prove2.me/theorems/7da9bf4b-afe8-4ee6-a01c-b0b11410a7ae
-- title:
--   Section5FiniteGridMeasure — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5FiniteGridMeasure; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5CellQuadrature
import Mathlib
section
set_option autoImplicit false

open MeasureTheory Set

/-! Exact finite quadrature, with arbitrary complex-valued data on the grid. -/

theorem section5_grid_sample_measurable (a δ : ℝ) : Measurable (section5_grid_sample a δ) := by
  unfold section5_grid_sample
  fun_prop

theorem section5_grid_sample_map_cell (a δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measure.map (section5_grid_sample a δ)
      (volume.restrict (Ico (a+j*δ) (a+(j+1)*δ))) =
      ENNReal.ofReal δ • Measure.dirac (a+j*δ) := by
  have heq : section5_grid_sample a δ =ᵐ[volume.restrict (Ico (a+j*δ) (a+(j+1)*δ))]
      fun _ => a+j*δ := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    exact section5_grid_sample_on_cell a δ hδ j x hx
  rw [Measure.map_congr heq,Measure.map_const]
  congr 1
  rw [Measure.restrict_apply_univ,Real.volume_Ico]
  congr 1
  ring

theorem section5_grid_sample_map_interval (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    Measure.map (section5_grid_sample a δ) (volume.restrict (Ico a (a+N*δ))) =
      ∑ j ∈ Finset.range N, ENNReal.ofReal δ • Measure.dirac (a+j*δ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hlow : a ≤ a+(N:ℝ)*δ := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have hhigh : a+(N:ℝ)*δ ≤ a+(N+1)*δ := by linarith
    have hunion : Ico a (a+(N+1)*δ) = Ico a (a+N*δ) ∪ Ico (a+N*δ) (a+(N+1)*δ) :=
      (Ico_union_Ico_eq_Ico hlow hhigh).symm
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hunion,Measure.restrict_union (Set.disjoint_left.mpr (by
      intro x hx hy
      exact (not_lt_of_ge hy.1) hx.2)) measurableSet_Ico,
      Measure.map_add _ _ (section5_grid_sample_measurable a δ),ih,
      section5_grid_sample_map_cell a δ hδ N,Finset.sum_range_succ]

theorem section5_grid_sample_map_count (a δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    Measure.map (section5_grid_sample a δ) (volume.restrict (Ico a (a+N*δ))) =
      Measure.map (fun j : Fin N => a+(j:ℝ)*δ)
        (ENNReal.ofReal δ • (Measure.count : Measure (Fin N))) := by
  rw [section5_grid_sample_map_interval a δ hδ N,Measure.map_smul,Measure.count]
  rw [Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_dirac,Measure.sum_fintype]
  rw [Finset.smul_sum]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ENNReal.ofReal δ • Measure.dirac (a+(j:ℝ)*δ)) N).symm

theorem section5_pi_scaled_count {β : Type*} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (n : ℕ) (δ : ℝ) :
    Measure.pi (fun _ : Fin n => ENNReal.ofReal δ • (Measure.count : Measure β)) =
      (ENNReal.ofReal δ)^n • (Measure.count : Measure (Fin n → β)) := by
  classical
  have : IsFiniteMeasure (ENNReal.ofReal δ • (Measure.count : Measure β)) := by
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp

theorem section5_grid_sample_map_pi (n N : ℕ) (a δ : ℝ) (hδ : 0 < δ) :
    Measure.map (fun x : Fin n → ℝ => fun i => section5_grid_sample a δ (x i))
      (Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ)))) =
      Measure.map (fun j : Fin n → Fin N => fun i => a+(j i:ℝ)*δ)
        ((ENNReal.ofReal δ)^n • (Measure.count : Measure (Fin n → Fin N))) := by
  have : IsFiniteMeasure (ENNReal.ofReal δ • (Measure.count : Measure (Fin N))) := by
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  rw [Measure.pi_map_pi (fun _ => (section5_grid_sample_measurable a δ).aemeasurable)]
  simp_rw [section5_grid_sample_map_count a δ hδ N]
  rw [← Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable),
    section5_pi_scaled_count n δ]





theorem section5_finite_grid_integrable (n N : ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    Integrable (fun x => F (fun i => section5_grid_sample a δ (x i)))
      (Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ)))) := by
  let μ := Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ)))
  have hround : Measurable (fun x : Fin n → ℝ => fun i => section5_grid_sample a δ (x i)) :=
    measurable_pi_lambda _ (fun i =>
      (section5_grid_sample_measurable a δ).comp (measurable_pi_apply i))
  apply (integrable_map_measure hF.aestronglyMeasurable hround.aemeasurable).mp
  rw [section5_grid_sample_map_pi n N a δ hδ]
  apply (integrable_map_measure hF.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr
  exact Integrable.of_finite.smul_measure (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

end


