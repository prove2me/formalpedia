-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:41:15.339641+00:00
-- url     : https://prove2.me/theorems/6fca32b6-1f81-48e6-9945-ae0ece7d9bbf
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRectSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRectSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F000
import Definitions.Def_SourceProof_5954de30c996278fc1ce5bc6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Rectangle-simple functions and their `L²` density

Finite `ℝ`-linear combinations of indicators of measurable rectangles `A ×ˢ B ⊆ Ω × E`, their
closure properties, and their density in `L²(μ)` for a finite measure `μ` on `Ω × E`. The
density is obtained from the monotone-class theorem over the rectangle π-system, so no countable
generation or standard-Borel hypothesis on `E` is required; a trimmed-product lemma transfers
`L²` bounds along a sub-σ-algebra of `Ω`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Mark discretisation via rectangle density (general `E`)

To turn the (mark-continuous) shifted dyadic eval into a genuine `SimplePredictable`,
we approximate the mark dependence by `ℝ`-linear combinations of indicators of
measurable rectangles `A ×ˢ B`. These are dense in `L²(μΩ ⊗ μE)` for *finite*
measures by the monotone-class theorem over the rectangle π-system
(`isPiSystem_prod`/`generateFrom_prod`) — **no countable-generation/standard-Borel
on `E` is needed**. -/

/-- Rectangle-approximability in `L²` is preserved under scalar multiplication. -/
lemma RectApprox.const_smul {μ : Measure (Ω × E)} {f : Ω × E → ℝ}
    (hf : RectApprox μ f) (c : ℝ) : RectApprox μ (c • f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    intro ε hε
    refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
    rw [show (0 : Ω × E → ℝ) - (fun _ => 0) = 0 from by funext x; simp,
      MeasureTheory.eLpNorm_zero]
    exact hε
  · intro ε hε
    have hcn : ‖c‖ₑ ≠ 0 := by simp [hc]
    obtain ⟨g, hg, hgerr⟩ := hf (ε / ‖c‖ₑ) (ENNReal.div_pos hε.ne' enorm_ne_top)
    refine ⟨c • g, hg.smul c, ?_⟩
    rw [show c • f - c • g = c • (f - g) from (smul_sub c f g).symm,
      MeasureTheory.eLpNorm_const_smul]
    calc ‖c‖ₑ * MeasureTheory.eLpNorm (f - g) 2 μ
        < ‖c‖ₑ * (ε / ‖c‖ₑ) := ENNReal.mul_lt_mul_right hcn enorm_ne_top hgerr
      _ = ε := ENNReal.mul_div_cancel hcn enorm_ne_top
/-- The indicator of a measurable set scaled by a constant is `L²`-approximable by
rectangle-simple functions (finite measure, **general `E`**). -/
lemma rectApprox_indicator_const (μ : Measure (Ω × E)) [IsFiniteMeasure μ]
    {s : Set (Ω × E)} (hs : MeasurableSet s) (c : ℝ) :
    RectApprox μ (s.indicator (fun _ => c)) := by
  have h := (_root_.Prove2MeSourceProof.h_5954de30c996278fc1ce5bc6 μ hs).const_smul c
  rwa [show c • s.indicator (fun _ => (1 : ℝ)) = s.indicator (fun _ => c) from by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]] at h
/-- **Rectangle-simple functions are dense in `L²(μ)`** for any finite measure `μ` on
`Ω × E`, with **no countable-generation/standard-Borel hypothesis on the mark space `E`**.
Reduces (via `MemLp.induction_dense`) to the indicator case `rectApprox_indicator_const`,
using closure of `IsRectSimple` under addition. -/
lemma rectSimple_dense_L2 (μ : Measure (Ω × E)) [IsFiniteMeasure μ] {f : Ω × E → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ ≤ ε := by
  obtain ⟨g, hgerr, hg⟩ := MeasureTheory.MemLp.induction_dense (by norm_num) IsRectSimple
    (fun c s hs hμs ε' hε' => by
      obtain ⟨g, hg, hgerr⟩ := rectApprox_indicator_const μ hs c ε' (pos_iff_ne_zero.mpr hε')
      exact ⟨g, by rw [MeasureTheory.eLpNorm_sub_comm]; exact hgerr.le, hg⟩)
    (fun f g hf hg => hf.add hg) (fun f hf => hf.aestronglyMeasurable μ) hf hε
  exact ⟨g, hg, hgerr⟩
/-- **Rectangle-simple `L²` approximating sequence.** Any `L²` function on `Ω × E`
(finite `μ`, **general `E`**) is the `L²`-limit of a sequence of rectangle-simple
functions — the form consumed by the `masterApprox` Cauchy/limit construction. -/
lemma rectSimple_L2_tendsto (μ : Measure (Ω × E)) [IsFiniteMeasure μ] {f : Ω × E → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) :
    ∃ g : ℕ → (Ω × E → ℝ), (∀ n, IsRectSimple (g n)) ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f - g n) 2 μ) Filter.atTop (nhds 0) := by
  choose g hg hgerr using fun n : ℕ =>
    rectSimple_dense_L2 μ hf (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))
  exact ⟨g, hg, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) hgerr⟩
omit [MeasurableSpace Ω] in
/-- **Trim–product iterated-lintegral bridge.** For a sub-σ-algebra `m ≤ m₀` on `Ω`
and an `m ⊗ E`-measurable `F : Ω × E → ℝ≥0∞`, the integral against the product
`(P.trim hm) ⊗ ν` equals the iterated integral against `ν` then `P`. (Tonelli on the
trimmed space, then `lintegral_trim` on the `m`-measurable inner integral.) -/
lemma lintegral_prod_trim_left
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} {ν : Measure E} [SigmaFinite ν]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {F : Ω × E → ℝ≥0∞} (hF : @Measurable (Ω × E) ℝ≥0∞ (m.prod inferInstance) _ F) :
    ∫⁻ q, F q ∂((P.trim hm).prod ν) = ∫⁻ ω, ∫⁻ e, F (ω, e) ∂ν ∂P := by
  rw [MeasureTheory.lintegral_prod _ hF.aemeasurable]
  exact MeasureTheory.lintegral_trim hm
    (@Measurable.lintegral_prod_right' Ω E m _ ν _ F hF)
end LevyStochCalc.Poisson.Compensated


