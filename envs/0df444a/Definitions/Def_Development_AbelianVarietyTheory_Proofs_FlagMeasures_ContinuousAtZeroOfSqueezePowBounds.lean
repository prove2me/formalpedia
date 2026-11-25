-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBounds
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContinuousAtZeroOfSqueezePowBounds
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:48.3399+00:00
-- url     : https://prove2.me/theorems/3567a725-d60d-47bc-a4fb-e95f79a8341e
-- title:
--   Continuous At Zero Of Squeeze Pow Bounds
-- statement:
--   Definitions and structural lemmas for Continuous At Zero Of Squeeze Pow Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ContinuousAtZeroOfSqueezePowBounds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace GlobalTheory
theorem squeeze_continuousAt_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)
    (f : V → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) :
    f 0 = c ∧ ContinuousAt f 0 := by
  have h1 : Tendsto (fun ε : ℝ => (1 + ε)⁻¹ ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).pow d
    simpa using this.tendsto
  have h2 : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by norm_num)).pow d
    simpa using this.tendsto
  have hL : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
    simpa using this
  have hU : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hc)
    simpa using this
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hf : Tendsto f (𝓝 0) (𝓝 c) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c :=
        nhdsWithin_le_nhds (hL.eventually (lt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_lt_of_le hε (hx x hxb).1
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c < a :=
        nhdsWithin_le_nhds (hU.eventually (gt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_le_of_lt (hx x hxb).2 hε
  have h0 : f 0 = c := tendsto_nhds_unique (tendsto_pure_nhds f 0) (hf.mono_left (pure_le_nhds 0))
  refine ⟨h0, ?_⟩
  unfold ContinuousAt
  rw [h0]
  exact hf
example : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 :=
  squeeze_continuousAt_zero
end GlobalTheory


