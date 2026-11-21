-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
-- name    : LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:17:02.300193+00:00
-- url     : https://prove2.me/theorems/de9e0202-444d-4b7d-abef-7879cc17f5e3
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRefinement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRefinement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/

omit [MeasurableSpace Ω] in
/-- **`‖M‖` is a submartingale.** For a real martingale `M`, `fun i ω => ‖M i ω‖` is a
submartingale: `‖Mᵢ‖ = ‖E[Mⱼ|ℱᵢ]‖ ≤ E[‖Mⱼ‖ ∣ ℱᵢ]` a.e. (conditional Jensen,
`norm_condExp_le`). -/
lemma martingale_norm_submartingale
    {ι : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ι mΩ}
    {μ : Measure Ω} {f : ι → Ω → ℝ} (hf : MeasureTheory.Martingale f ℱ μ) :
    MeasureTheory.Submartingale (fun i ω => ‖f i ω‖) ℱ μ := by
  refine ⟨fun i => (hf.stronglyMeasurable i).norm, fun i j hij => ?_,
    fun i => (hf.integrable i).norm⟩
  have hmg : f i =ᵐ[μ] μ[f j | ℱ i] := (hf.2 i j hij).symm
  filter_upwards [hmg, norm_condExp_le (μ := μ) (m := ℱ i) (f := f j)]
    with ω h1 h2
  rw [h1]; exact h2
omit [MeasurableSpace Ω] in
/-- **`L¹`-tail Doob maximal inequality.** For a real martingale `M` on a finite measure,
`μ{ supₖ≤N ‖Mₖ‖ ≥ ε } ≤ E[‖M_N‖] / ε`. From `maximal_ineq` applied to the submartingale
`‖M‖`, bounding the set-integral by the full integral. -/
lemma martingale_norm_tail_maximal
    {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ℕ mΩ} {μ : Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {M : ℕ → Ω → ℝ} (hf : MeasureTheory.Martingale M ℱ μ)
    (N : ℕ) {ε : ℝ≥0} (hε : 0 < ε) :
    μ {ω | (ε : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        (fun k => ‖M k ω‖)} ≤ ENNReal.ofReal (∫ ω, ‖M N ω‖ ∂μ) / ε := by
  have hmax := MeasureTheory.maximal_ineq (martingale_norm_submartingale hf)
    (fun _ _ => norm_nonneg _) (ε := ε) N
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hε.ne')) (Or.inl (by simp)),
    mul_comm]
  refine le_trans hmax (ENNReal.ofReal_le_ofReal ?_)
  exact MeasureTheory.setIntegral_le_integral (hf.integrable N).norm
    (Filter.Eventually.of_forall (fun ω => norm_nonneg _))
/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

end LevyStochCalc.Poisson.Compensated


