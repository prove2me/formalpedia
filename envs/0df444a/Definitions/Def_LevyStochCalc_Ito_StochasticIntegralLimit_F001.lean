-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
-- name    : LevyStochCalc_Ito_StochasticIntegralLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:46:25.116053+00:00
-- url     : https://prove2.me/theorems/33a80fcd-62bb-48b4-bd29-e1da87743ae7
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

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

/-- A section in the sample point of a jointly measurable nonnegative marked kernel has a
measurable mark integral. -/
theorem measurable_section_markLIntegral {f : Ω → ℝ → E → ℝ≥0∞}
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) (ω : Ω) :
    Measurable fun s => ∫⁻ e, f ω s e ∂ν := by
  have hcurry : Measurable fun q : ℝ × E => f ω q.1 q.2 :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  exact hcurry.lintegral_prod_right'
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


