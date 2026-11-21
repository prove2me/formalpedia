-- Prove2me | Definitions.Def_SourceProof_02f6bb3f77d8e99b477dbb5c
-- name    : SourceProof_02f6bb3f77d8e99b477dbb5c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:12:11.225166+00:00
-- url     : https://prove2.me/theorems/6386988f-1ed7-4a5d-a4f6-2543d376046b
-- title:
--   LevyStochCalc source module: SourceProof_02f6bb3f77d8e99b477dbb5c
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram` comes from the `LevyStochCalc.Poisson.CompensatedLinear` module. The staged Lean declaration includes its source proof and dependency references.
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

theorem _root_.Prove2MeSourceProof.h_02f6bb3f77d8e99b477dbb5c
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e)
        + markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = 2 * markedEnergy P ν T φ₁ + 2 * markedEnergy P ν T φ₂ := by
  have hma : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 + φ₂ p.1 p.2.1 p.2.2 :=
    hm₁.add hm₂
  have hpt : ∀ a b : ℝ, (‖a + b‖₊ : ℝ≥0∞) ^ 2 + (‖a - b‖₊ : ℝ≥0∞) ^ 2
      = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
    intro a b
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq,
      LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hmark : ∀ (ω : Ω) (s : ℝ),
      (∫⁻ e, (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + ∫⁻ e, (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        = 2 * (∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          + 2 * ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    intro ω s
    have k1 : Measurable fun e => (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hm₁.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    have k2 : Measurable fun e => (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hm₂.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    have ka : Measurable fun e => (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
      ((measurable_nnnorm.comp ((hma.comp (measurable_prodMk_left (x := ω))).comp
        (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal).pow_const 2
    rw [← lintegral_add_left ka, ← lintegral_const_mul 2 k1, ← lintegral_const_mul 2 k2,
      ← lintegral_add_left (k1.const_mul 2)]
    exact lintegral_congr fun e => hpt _ _
  have htime : ∀ ω : Ω,
      LevyStochCalc.Poisson.Compensated.markedDensity ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) ω
          + LevyStochCalc.Poisson.Compensated.markedDensity ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) ω
        = 2 * LevyStochCalc.Poisson.Compensated.markedDensity ν T φ₁ ω + 2 * LevyStochCalc.Poisson.Compensated.markedDensity ν T φ₂ ω := by
    intro ω
    have sa := LevyStochCalc.Poisson.Compensated.measurable_markSlice (ν := ν)
      (φ := fun ω s e => φ₁ ω s e + φ₂ ω s e) hma ω
    have s1 := LevyStochCalc.Poisson.Compensated.measurable_markSlice (ν := ν) (φ := φ₁) hm₁ ω
    have s2 := LevyStochCalc.Poisson.Compensated.measurable_markSlice (ν := ν) (φ := φ₂) hm₂ ω
    rw [LevyStochCalc.Poisson.Compensated.markedDensity, LevyStochCalc.Poisson.Compensated.markedDensity, LevyStochCalc.Poisson.Compensated.markedDensity, LevyStochCalc.Poisson.Compensated.markedDensity,
      ← lintegral_add_left sa, ← lintegral_const_mul 2 s1, ← lintegral_const_mul 2 s2,
      ← lintegral_add_left (s1.const_mul 2)]
    exact lintegral_congr fun s => hmark ω s
  have e1 := LevyStochCalc.Poisson.Compensated.measurable_markedDensity (ν := ν) (φ := φ₁) hm₁ T
  have e2 := LevyStochCalc.Poisson.Compensated.measurable_markedDensity (ν := ν) (φ := φ₂) hm₂ T
  have ea := LevyStochCalc.Poisson.Compensated.measurable_markedDensity (ν := ν)
    (φ := fun ω s e => φ₁ ω s e + φ₂ ω s e) hma T
  rw [LevyStochCalc.Poisson.Compensated.markedEnergy, LevyStochCalc.Poisson.Compensated.markedEnergy, LevyStochCalc.Poisson.Compensated.markedEnergy, LevyStochCalc.Poisson.Compensated.markedEnergy]
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = LevyStochCalc.Poisson.Compensated.markedDensity ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e) from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = LevyStochCalc.Poisson.Compensated.markedDensity ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = LevyStochCalc.Poisson.Compensated.markedDensity ν T φ₁ from rfl,
    show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = LevyStochCalc.Poisson.Compensated.markedDensity ν T φ₂ from rfl,
    ← lintegral_add_left ea, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  exact lintegral_congr fun ω => htime ω
end Parallelogram

section Linearity

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

end Linearity

end LevyStochCalc.Poisson.Compensated


