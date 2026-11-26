-- Prove2me | solution 1 for Auto.aux_card_le_sharp_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:14.679668+00:00
-- url     : https://prove2.me/submissions/0cb3c74f-d32a-42b8-bb2e-c7807b47f1fb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {d : ℕ} {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s)
    (t : Finset (EuclideanSpace ℝ (Fin d)))
    (ht : ∀ c ∈ t, ‖c‖ ≤ s)
    (htsep : ∀ c ∈ t, ∀ e ∈ t, c ≠ e → r ≤ ‖c - e‖) :
    (t.card : ℝ) ≤ (3 * s / r) ^ d := by
  let E := EuclideanSpace ℝ (Fin d)
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := r / 2
  let ρ : ℝ := s + r / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hρ : 0 < ρ := by
    dsimp [ρ]
    linarith
  set A : Set E := ⋃ c ∈ t, ball c δ with hA
  have D : Set.Pairwise (t : Set E) (Disjoint on fun c ↦ ball c δ) := by
    rintro c hc e he hce
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    convert htsep c hc e he hce using 1
    all_goals
      dsimp [δ]
      ring
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun c hc ↦ ?_
    apply ball_subset_ball'
    calc
      δ + dist c 0 ≤ δ + s := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (ht c hc)
      _ = ρ := by
        dsimp [δ, ρ]
        ring
  have I :
      (t.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      (t.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ ↦ measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hρ]
  have J : (t.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 I
  have K : (t.card : ℝ) ≤ (ρ / δ) ^ Module.finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
    have hδpow : 0 < δ ^ Module.finrank ℝ E := pow_pos hδ _
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at h
    rw [div_pow]
    exact (le_div_iff₀ hδpow).2 h
  have hratio : ρ / δ ≤ 3 * s / r := by
    dsimp [ρ, δ]
    field_simp
    nlinarith
  calc
    (t.card : ℝ) ≤ (ρ / δ) ^ Module.finrank ℝ E := K
    _ ≤ (3 * s / r) ^ Module.finrank ℝ E :=
      pow_le_pow_left₀ (div_nonneg (by dsimp [ρ]; linarith) hδ.le) hratio _
    _ = (3 * s / r) ^ d := by simp [E]
end Auto
