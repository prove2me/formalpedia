-- Prove2me | Definitions.Def_Thm_ShorNonsmooth_Stochastic_condExp_lam
-- name    : Thm_ShorNonsmooth_Stochastic_condExp_lam
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-20T18:43:48.651873+00:00
-- url     : https://prove2.me/theorems/31ae09c1-2343-4d27-95a4-7b1e1082bccc
-- title:
--   Conditional expectation of pointwise sums, differences and products, in lambda form

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology

namespace ShorNonsmooth.Stochastic

/-- Conditional expectation of a pointwise sum, in lambda form:
`μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m]`. -/
theorem condExp_add_lam {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := by
  have h := condExp_add hf hg m
  have h1 : μ[f + g | m] =ᵐ[μ] μ[fun ω => f ω + g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω + g ω | m] =ᵐ[μ] μ[f | m] + μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]

/-- Conditional expectation of a pointwise difference, in lambda form:
`μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m]`. -/
theorem condExp_sub_lam {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m] := by
  have h := condExp_sub hf hg m
  have h1 : μ[f - g | m] =ᵐ[μ] μ[fun ω => f ω - g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω - g ω | m] =ᵐ[μ] μ[f | m] - μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]

/-- Conditional expectation of a pointwise product, in lambda form:
`μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m]`. -/
theorem condExp_mul_lam {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := by
  have h := condExp_mul_of_aestronglyMeasurable_left (m := m) hf hfg hg
  have h1 : μ[f * g | m] =ᵐ[μ] μ[fun ω => f ω * g ω | m] :=
    condExp_congr_ae (m := m) (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have h2 : μ[fun ω => f ω * g ω | m] =ᵐ[μ] f * μ[g | m] := h1.symm.trans h
  filter_upwards [h2] with ω hω
  rw [hω]

end ShorNonsmooth.Stochastic


