-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
-- name    : LevyStochCalc_Poisson_CompensatedLinear_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:10:59.251066+00:00
-- url     : https://prove2.me/theorems/7beee342-4c83-45c9-adaf-8fee7bafb435
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

omit [IsProbabilityMeasure P] in
/-- A marked integrand dominated pointwise by twice the sum of two others has energy bounded by
twice the sum of theirs. -/
theorem markedEnergy_le_two_mul_add {ψ : Ω → ℝ → E → ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T ψ ≤ 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by
  have e1 := measurable_markedDensity (ν := ν) (φ := φ₁) hm₁ T
  have e2 := measurable_markedDensity (ν := ν) (φ := φ₂) hm₂ T
  rw [markedEnergy, markedEnergy, markedEnergy,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ₁ from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = markedDensity ν T φ₂ from rfl,
    ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  have s1 := measurable_markSlice (ν := ν) (φ := φ₁) hm₁ ω
  have s2 := measurable_markSlice (ν := ν) (φ := φ₂) hm₂ ω
  rw [markedDensity, markedDensity, ← lintegral_const_mul 2 s1, ← lintegral_const_mul 2 s2,
    ← lintegral_add_left (s1.const_mul 2)]
  refine lintegral_mono fun s => ?_
  have k1 : Measurable fun e => (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm₁.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  have k2 : Measurable fun e => (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((measurable_nnnorm.comp ((hm₂.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
  rw [← lintegral_const_mul 2 k1, ← lintegral_const_mul 2 k2,
    ← lintegral_add_left (k1.const_mul 2)]
  refine lintegral_mono fun e => ?_
  calc (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2) := hbound ω s e
    _ = 2 * (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 := by ring
omit [IsProbabilityMeasure P] in
/-- A marked integrand dominated by twice the sum of two square-integrable energies is itself
square integrable. -/
theorem markedEnergy_lt_top_of_bound {ψ : Ω → ℝ → E → ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hq₁ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₁ < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ₂ < ⊤) :
    ∀ T : ℝ, 0 < T → markedEnergy P ν T ψ < ⊤ := fun T hT =>
  lt_of_le_of_lt (markedEnergy_le_two_mul_add hbound hm₁ hm₂ T) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp) (hq₁ T hT), ENNReal.mul_lt_top (by simp) (hq₂ T hT)⟩)
omit [IsProbabilityMeasure P] in
/-- The same bound in the `≠ ⊤` form, at a single horizon. -/
theorem markedEnergy_ne_top_of_bound {ψ : Ω → ℝ → E → ℝ} {T : ℝ}
    (hbound : ∀ ω s e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h1 : markedEnergy P ν T φ₁ ≠ ⊤) (h2 : markedEnergy P ν T φ₂ ≠ ⊤) :
    markedEnergy P ν T ψ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by simp) h1, ENNReal.mul_ne_top (by simp) h2⟩)
    (markedEnergy_le_two_mul_add hbound hm₁ hm₂ T)
omit [IsProbabilityMeasure P] in
/-- The energy of a sum is finite when both energies are. -/
theorem markedEnergy_add_ne_top {T : ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h1 : markedEnergy P ν T φ₁ ≠ ⊤) (h2 : markedEnergy P ν T φ₂ ≠ ⊤) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) ≠ ⊤ :=
  markedEnergy_ne_top_of_bound (fun _ _ _ => sq_nnnorm_add_le_two_mul _ _) hm₁ hm₂ h1 h2
end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in
/-- The compensated integral is square integrable. -/
theorem stochasticIntegral_memLp (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤) (T : ℝ) :
    MemLp (stochasticIntegral N ℱ hℱ φ hm hp hq T) 2 P :=
  MemLp.ae_eq (stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq T).symm
    (process_memLp N ℱ hℱ φ hm hp hq T)
end Linearity

end LevyStochCalc.Poisson.Compensated


