-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002
-- name    : LevyStochCalc_Poisson_CompensatedLinear_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:12:07.047073+00:00
-- url     : https://prove2.me/theorems/1e78623e-9e04-4340-a586-7a43f9259a15
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedLinear
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedLinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F000

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

omit [IsProbabilityMeasure P] in
/-- Scaling a marked integrand scales its energy by the square of the scalar. -/
theorem lintegral_markedEnergy_const_mul {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (c T : ℝ) :
    markedEnergy P ν T (fun ω s e => c * φ ω s e)
      = ENNReal.ofReal (c ^ 2) * markedEnergy P ν T φ := by
  have hpt : ∀ a : ℝ, (‖c * a‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (c ^ 2) * (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro a
    rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  have e := measurable_markedDensity (ν := ν) (φ := φ) hm T
  rw [markedEnergy, markedEnergy,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ from rfl, ← lintegral_const_mul _ e]
  refine lintegral_congr fun ω => ?_
  have s1 := measurable_markSlice (ν := ν) (φ := φ) hm ω
  rw [markedDensity, ← lintegral_const_mul _ s1]
  refine lintegral_congr fun s => ?_
  have k1 : Measurable fun e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  rw [← lintegral_const_mul _ k1]
  exact lintegral_congr fun e => hpt _
omit [IsProbabilityMeasure P] in
/-- The energy of a scalar multiple is finite when the energy is. -/
theorem markedEnergy_const_mul_ne_top {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (h : markedEnergy P ν T φ ≠ ⊤) (c : ℝ) :
    markedEnergy P ν T (fun ω s e => c * φ ω s e) ≠ ⊤ := by
  rw [lintegral_markedEnergy_const_mul (P := P) (ν := ν) hm c T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
end Linearity

end LevyStochCalc.Poisson.Compensated


