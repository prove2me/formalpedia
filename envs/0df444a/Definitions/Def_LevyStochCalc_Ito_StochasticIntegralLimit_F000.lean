-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
-- name    : LevyStochCalc_Ito_StochasticIntegralLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:46:12.138776+00:00
-- url     : https://prove2.me/theorems/7d092fd4-28bc-4829-8f30-2eb4135f4fe3
-- title:
--   Source declarations: LevyStochCalc.Ito.StochasticIntegralLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.StochasticIntegralLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

/-- Dominated convergence for a sequence of nonnegative functions tending to `0`. -/
theorem tendsto_lintegral_of_dominated_tendsto_zero {μ : Measure α} {F : ℕ → α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF : ∀ m, AEMeasurable (F m) μ) (hb : ∀ m, F m ≤ᵐ[μ] bound)
    (hfin : ∫⁻ a, bound a ∂μ ≠ ⊤)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun m => F m a) atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ a, F m a ∂μ) atTop (𝓝 0) := by
  have h := MeasureTheory.tendsto_lintegral_of_dominated_convergence' (μ := μ) (F := F)
    (f := fun _ => (0 : ℝ≥0∞)) bound hF hb hfin hlim
  simpa using h
/-- Two reals whose norms are bounded by `c` differ by at most `2 c` in the squared extended
norm. -/
theorem sq_enorm_sub_le_of_norm_le {u v c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c) :
    (‖u - v‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (norm_nonneg u) hu
  have habs : |u - v| ≤ 2 * |c| := by
    rw [abs_of_nonneg hc0]
    have h1 : |u - v| ≤ |u| + |v| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    have h2 : |u| + |v| ≤ c + c := add_le_add hu hv
    linarith
  have h := LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le (c := 2) (by norm_num) habs
  simpa [show ((2 : ℝ≥0∞)) ^ 2 = 4 from by norm_num] using h
/-- The square of the extended norm of a sequence of reals converging to a limit tends to `0`
after subtracting the limit. -/
theorem tendsto_sq_enorm_sub {f : ℕ → ℝ} {a : ℝ} (h : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => f m - a) atTop (𝓝 0) := by
    simpa using h.sub_const a
  have h2 : Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0)) atTop (𝓝 0) := by simpa using h1.nnnorm
  have h3 : Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0) ^ 2) atTop (𝓝 0) := by simpa using h2.pow 2
  simpa [ENNReal.coe_pow] using ENNReal.tendsto_coe.2 h3
end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Compensated

section MarkCut

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m))

end MarkCut

end LevyStochCalc.Ito.IntegralLimit


