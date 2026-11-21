-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_GeneratorModification_F000
-- name    : LevyStochCalc_BSDEJ_GeneratorModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:34.360653+00:00
-- url     : https://prove2.me/theorems/ea97fc57-7384-400f-8bf8-4e7c8f7e0d77
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.GeneratorModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.GeneratorModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorAlongMarkStep_F000
import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F000
import Definitions.Def_LevyStochCalc_BSDEJ_GeneratorEnergy_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressively measurable version of the generator along a triple of processes

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable is
not assumed measurable in the jump variable, so the composite `(ω, s) ↦ f s (Y s ω) (Z s ω)
(U s ω)` along a triple of processes need not be measurable. Approximating the marked process `U`
in `L²` by mark-step integrands makes the composite the pointwise limit, along a subsequence and
almost everywhere on `Ω × [0, T]`, of the jointly and progressively measurable processes obtained
by evaluating the generator along the approximants; the pointwise `limsup` of that subsequence is
then a progressively measurable process of finite energy, vanishing off the horizon, which agrees
with the composite almost everywhere.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

/-! ### Almost everywhere convergence from summable integrals -/

/-- The geometric series of ratio `2⁻¹` in `ℝ≥0∞` is finite. -/
theorem tsum_geometric_two_inv_ne_top : ∑' i : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.2 ?_
  rw [Ne, tsub_eq_zero_iff_le]
  exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))
/-- A sequence in `ℝ≥0∞` tending to zero has a subsequence dominated by the geometric sequence
of ratio `2⁻¹`. -/
theorem exists_subseq_lt_geometric {u : ℕ → ℝ≥0∞} (h : Tendsto u atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ i : ℕ, u (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, i ≤ j ∧ u j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i :=
      pos_iff_ne_zero.mpr (pow_ne_zero i (by simp))
    obtain ⟨n, hn⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
    exact ⟨max n i, le_max_right n i, hn (max n i) (le_max_left n i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩
/-- Nonnegative measurable functions with summable integrals tend to zero almost everywhere. -/
theorem ae_tendsto_zero_of_tsum_lintegral_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Tendsto (fun i => g i a) atTop (𝓝 0) := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne
/-- A real sequence whose extended distance to a point is dominated by a sequence tending to
zero converges to that point. -/
theorem tendsto_of_enorm_sub_le {u : ℕ → ℝ} {w : ℝ} {c : ℕ → ℝ≥0∞}
    (hle : ∀ i, (‖w - u i‖₊ : ℝ≥0∞) ≤ c i) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 w) := by
  have h0 : Tendsto (fun i => ((‖w - u i‖₊ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le) hle
  have h1 : Tendsto (fun i => ‖w - u i‖₊) atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_coe]
    simpa using h0
  have h2 : Tendsto (fun i => ‖w - u i‖) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrw : (fun i => ‖w - u i‖) = fun i => ‖u i - w‖ := funext fun i => norm_sub_rev _ _
  rwa [hrw] at h2
/-! ### The generator along a triple of processes -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-- A generator Lipschitz in the state variables is, at fixed time and fixed `(y, z)`, Lipschitz
in the jump variable for the `L²(ν)` distance. -/
theorem enorm_sub_generator_jump_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ) :
    (‖f s y z u₁ - f s y z u₂‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal L * (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have key := hlip s y y z z u₁ u₂
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, zero_add] at key
  exact key
variable [IsProbabilityMeasure P] [SigmaFinite ν] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

end LevyStochCalc.BSDEJ.Generator


