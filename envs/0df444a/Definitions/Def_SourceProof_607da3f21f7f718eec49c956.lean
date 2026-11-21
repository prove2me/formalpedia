-- Prove2me | Definitions.Def_SourceProof_607da3f21f7f718eec49c956
-- name    : SourceProof_607da3f21f7f718eec49c956
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:13.619371+00:00
-- url     : https://prove2.me/theorems/1cf846a8-540c-4636-af57-ad74cfeab7ce
-- title:
--   LevyStochCalc source module: SourceProof_607da3f21f7f718eec49c956
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_const_mul` comes from the `LevyStochCalc.Poisson.CompensatedLinear` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002
import Definitions.Def_SourceProof_b2a8a79da4bd7b154436ee26

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated Poisson integral

The compensated integral is built as an `L²` limit of elementary integrals, which is not itself a
linear construction, so linearity comes from the isometries instead: they fix every squared
`L²`-distance among the integrals of two integrands and of their sum, and the parallelogram law
for the marked energies then forces the sum relation. The same three-distance argument gives the
scalar rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Parallelogram

variable {φ₁ φ₂ : Ω → ℝ → E → ℝ}

end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_607da3f21f7f718eec49c956 {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤) (c : ℝ)
    (hmc : Measurable fun p : Ω × ℝ × E => c * φ p.1 p.2.1 p.2.2)
    (hpc : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => c * φ ω s e)
    (hqc : ∀ T : ℝ, 0 < T → markedEnergy P ν T (fun ω s e => c * φ ω s e) < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T
      =ᵐ[P] fun ω => c * stochasticIntegral N ℱ hℱ φ hm hp hq T ω := by
  have hscale : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖c * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
    LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_const_mul (P := P) (ν := ν) (φ := φ) hm c T
  have hdiff : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖c * φ ω s e - φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ENNReal.ofReal ((c - 1) ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
    refine Eq.trans ?_
      (LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_const_mul (P := P) (ν := ν) (φ := φ) hm (c - 1) T)
    exact lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => by ring_nf
  refine _root_.Prove2MeSourceProof.h_b2a8a79da4bd7b154436ee26
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T)
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hm hp hq T)
    (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ (fun ω s e => c * φ ω s e) hmc hpc hqc T hT)
    (LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ hm hp hq T hT)
    (LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ (fun ω s e => c * φ ω s e) φ hmc hm hpc hp
      hqc hq T hT) ?_ ?_
  · rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg c)]
  · rw [hdiff, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (c - 1))]
end Linearity

end LevyStochCalc.Poisson.Compensated


