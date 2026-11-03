-- Prove2me | Definitions.Def_LeanLevy_Probability_WeakConvergence
-- name    : LeanLevy_Probability_WeakConvergence
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:59:50.234377+00:00
-- url     : https://prove2.me/theorems/7bdafbd2-0131-4c1e-97fd-88f08370d8f2
-- title:
--   LeanLevy source module: Probability.WeakConvergence
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Probability.WeakConvergence`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Probability_Characteristic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Sequences

/-!
# Weak Convergence and Lévy's Continuity Theorem

This file proves Lévy's continuity theorem: a sequence of probability measures
on ℝ converges weakly if and only if their characteristic functions converge
pointwise.

## Main definitions

* `MeasureTheory.ProbabilityMeasure.CharFunTendsto` — pointwise convergence of
  characteristic functions along a filter.

## Main results

* `MeasureTheory.ProbabilityMeasure.charFunTendsto_of_tendsto` — weak convergence
  implies pointwise convergence of characteristic functions.
* `MeasureTheory.ProbabilityMeasure.isTight_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies tightness of the sequence.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies weak convergence (Lévy's continuity theorem).
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_charFunTendsto` — the biconditional.

## References

* [P. Billingsley, *Convergence of Probability Measures*]
-/

open MeasureTheory Complex ComplexConjugate Filter Topology BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

variable {ι : Type*} {F : Filter ι}

/-- Pointwise convergence of characteristic functions of probability measures
along a filter `F`. -/
def CharFunTendsto (μs : ι → ProbabilityMeasure ℝ) (F : Filter ι)
    (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ ξ : ℝ, Tendsto (fun i => characteristicFun (μs i) ξ) F (𝓝 (characteristicFun μ ξ))



/-- The exponential character `x ↦ exp(iξx)` as a bounded continuous function. -/
noncomputable def expBCF (ξ : ℝ) : ℝ →ᵇ ℂ :=
  .mkOfBound ⟨fun x => exp (↑(ξ * x) * I), by fun_prop⟩ 2
    (fun x y => by
      calc dist (exp (↑(ξ * x) * I)) (exp (↑(ξ * y) * I))
          ≤ ‖exp (↑(ξ * x) * I)‖ + ‖exp (↑(ξ * y) * I)‖ := dist_le_norm_add_norm _ _
        _ = 1 + 1 := by simp only [norm_exp_ofReal_mul_I]
        _ = 2 := by ring)

theorem integral_expBCF_eq_characteristicFun (μ : ProbabilityMeasure ℝ) (ξ : ℝ) :
    ∫ x, expBCF ξ x ∂(μ : Measure ℝ) = characteristicFun μ ξ := by
  simp only [characteristicFun, charFun_apply_real]
  congr 1; ext x
  simp only [expBCF, mkOfBound_coe, ContinuousMap.coe_mk]
  push_cast; ring

/-- **Easy direction of Lévy's continuity theorem.** Weak convergence of probability
measures implies pointwise convergence of characteristic functions. -/
theorem charFunTendsto_of_tendsto {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μs F (𝓝 μ)) : CharFunTendsto μs F μ := by
  intro ξ
  simp_rw [← integral_expBCF_eq_characteristicFun]
  exact (tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h (expBCF ξ)

/-! ### Tightness from characteristic function convergence -/

section Tightness

open Set MeasureTheory ENNReal Metric



-- The tail bound 2⁻¹ * r * ‖∫ t in (-2*r⁻¹)..(2*r⁻¹), 1 - charFun μ t‖ → 0 as r → ∞.
-- Proof: charFun μ is continuous with charFun μ 0 = 1, so 1 - charFun μ t → 0 as t → 0.
-- The interval length is 4/r → 0, and the integrand is bounded, so the integral
-- is O(1/r) * O(sup on [-2/r, 2/r]) → 0.


/-- Generalized tail bound: for any continuous `φ` with `φ 0 = 1`, the quantity
`2⁻¹ * r * ‖∫ t in (-2/r)..(2/r), 1 - φ t‖ → 0` as `r → ∞`.

Same proof as `tendsto_tail_bound_of_charFun` with `charFun μ` replaced by abstract `φ`. -/
theorem tendsto_tail_bound_of_continuous
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : φ 0 = 1) :
    Tendsto (fun r => 2⁻¹ * r *
      ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖)
      atTop (𝓝 0) := by
  set f : ℝ → ℂ := fun t => 1 - φ t with hf_def
  have hf_cont : Continuous f := continuous_const.sub hφc
  have hf_zero : f 0 = 0 := by simp [hf_def, hφ0]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf_cont_at : ContinuousAt f 0 := hf_cont.continuousAt
  rw [ContinuousAt, hf_zero, Metric.tendsto_nhds] at hf_cont_at
  have hev := hf_cont_at (ε / 4) (by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη_pos, hη⟩ := hev
  refine ⟨max (2 / η + 1) 1, fun r hr => ?_⟩
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_of_max_le_right hr)
  have hr_ge : r ≥ 2 / η + 1 := le_of_max_le_left hr
  have h2r_lt : 2 * r⁻¹ < η := by
    rw [show (2 : ℝ) * r⁻¹ = 2 / r from by ring]
    calc 2 / r < 2 / (2 / η) := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 2)
            (by positivity) (by linarith)
      _ = η := by field_simp
  have h2r_pos : (0 : ℝ) < 2 * r⁻¹ := by positivity
  have hf_bound : ∀ t ∈ Set.uIoc (-2 * r⁻¹) (2 * r⁻¹), ‖f t‖ ≤ ε / 4 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -2 * r⁻¹ ≤ 2 * r⁻¹)] at ht
    have ht_abs : |t| < η := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have ht_dist : dist t 0 < η := by rwa [Real.dist_eq, sub_zero]
    have := hη ht_dist
    rw [dist_zero_right] at this
    exact le_of_lt this
  have hintegral_bound : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤
      ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hf_bound
  have habs : |2 * r⁻¹ - (-2 * r⁻¹)| = 4 * r⁻¹ := by
    rw [show 2 * r⁻¹ - (-2 * r⁻¹) = 4 * r⁻¹ from by ring]
    exact abs_of_pos (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hint_le : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤ ε / 4 * (4 * r⁻¹) := by
    calc ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖
        ≤ ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| := hintegral_bound
      _ = ε / 4 * (4 * r⁻¹) := by rw [habs]
  have h2r_nonneg : (0 : ℝ) ≤ 2⁻¹ * r := by positivity
  have hle := mul_le_mul_of_nonneg_left hint_le h2r_nonneg
  have hstep : 2⁻¹ * r * (ε / 4 * (4 * r⁻¹)) = ε / 2 := by field_simp
  linarith

/-- Generalized radius/threshold: for a sequence of probability measures whose charfuns
converge pointwise to a continuous `φ` with `φ 0 = 1`, there exist r > 0 and n₀ such that
for all n ≥ n₀, the tail measure (μs n){x | r < |x|} < δ. -/
theorem exists_radius_and_threshold_of_continuous_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : φ 0 = 1)
    (hconv : ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (_ : 0 < r) (n₀ : ℕ),
      ∀ n, n₀ ≤ n → (μs n : Measure ℝ).real {x | r < |x|} < δ := by
  -- Choose r₀ large enough that the tail bound for abstract φ is < δ/2
  have hlim := tendsto_tail_bound_of_continuous hφc hφ0
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨r₀, hr₀⟩ := hlim (δ / 2) (half_pos hδ)
  set r := max r₀ 1 with hr_def
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hr_ge : r₀ ≤ r := le_max_left _ _
  have hφ_bound : 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - φ t‖ < δ / 2 := by
    have := hr₀ r hr_ge
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg] at this
    positivity
  -- The integral for μₙ converges to the integral for φ on [-2/r, 2/r]
  have hneg_rw : -(2 * r⁻¹) = -2 * r⁻¹ := by ring
  have hconv₀ : Tendsto
      (fun n => ∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - charFun (μs n : Measure ℝ) t)
      atTop (𝓝 (∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t)) := by
    rw [show (-2 * r⁻¹ : ℝ) = -(2 * r⁻¹) from by ring]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 2)
    · exact Eventually.of_forall fun n =>
        (stronglyMeasurable_const.sub stronglyMeasurable_charFun).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all _ fun t _ => norm_one_sub_charFun_le_two
    · exact intervalIntegrable_const
    · apply ae_of_all; intro t _
      exact tendsto_const_nhds.sub (hconv t)
  have hconv_scaled : Tendsto
      (fun n => 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - charFun (μs n : Measure ℝ) t‖) atTop
      (𝓝 (2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - φ t‖)) :=
    hconv₀.norm.const_mul _
  have hev : ∀ᶠ n in atTop, 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ < δ := by
    apply (hconv_scaled.eventually (Iio_mem_nhds hφ_bound)).mono
    intro n hn
    calc 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
            (1 : ℂ) - charFun (μs n : Measure ℝ) t‖
        < δ / 2 := hn
      _ < δ := half_lt_self hδ
  obtain ⟨n₀, hn₀⟩ := hev.exists_forall_of_atTop
  refine ⟨r, hr_pos, n₀, fun n hn => ?_⟩
  calc (μs n : Measure ℝ).real {x | r < |x|}
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
          (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ :=
        measureReal_abs_gt_le_integral_charFun hr_pos
    _ < δ := hn₀ n hn





end Tightness

/-! ### Lévy's continuity theorem -/





/-! ### Convenience API -/







end MeasureTheory.ProbabilityMeasure


