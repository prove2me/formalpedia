-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002
-- name    : LevyStochCalc_Poisson_CompensatedPullOut_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:24.449632+00:00
-- url     : https://prove2.me/theorems/9a99413e-2fce-4fec-bbfc-00d06f61240c
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedPullOut
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedPullOut in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F001
import Definitions.Def_SourceProof_ec4d5d34845b027c60491406

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

end Vanishing

section Weighted

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The energy of a boundedly weighted integrand is finite when the energy is. -/
theorem markedEnergy_mul_ne_top {φ : Ω → ℝ → E → ℝ} {T : ℝ} (h : markedEnergy P ν T φ ≠ ⊤)
    {V : Ω → ℝ} {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    markedEnergy P ν T (fun ω s e => V ω * φ ω s e) ≠ ⊤ := by
  have hM : ENNReal.ofReal (M ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hM h) ?_
  unfold markedEnergy
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun s => ?_
  rw [← lintegral_const_mul' _ _ hM]
  refine lintegral_mono fun e => ?_
  rw [coe_nnnorm_sq_eq_ofReal_sq, coe_nnnorm_sq_eq_ofReal_sq,
    ← ENNReal.ofReal_mul (sq_nonneg M)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow, ← sq_abs (V ω)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2) (sq_nonneg _)
namespace MarkedHorizonIntegrand

variable {T : ℝ}

/-- A marked integrand vanishing up to `a`, multiplied by a bounded weight measurable at `a`. -/
noncomputable def mulLeft (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ}
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V)
    {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) : MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => V ω * G.toFun ω s e
  measurable_uncurry :=
    ((hVm.measurable.mono (ℱ.le a) le_rfl).comp measurable_fst).mul G.measurable_uncurry
  progressive := _root_.Prove2MeSourceProof.h_ec4d5d34845b027c60491406 G.progressive hGa hVm
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_mul_ne_top G.energy_ne_top hVb
variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

/-- The compensated integral depends only on the underlying process. -/
theorem integral_congr_toFun {G₁ G₂ : MarkedHorizonIntegrand P ν ℱ T} (h : G₁.toFun = G₂.toFun) :
    G₁.integral N hℱ = G₂.integral N hℱ := by
  cases G₁
  cases G₂
  cases h
  rfl
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator of a weighted integrand is the squared weight times the compensator. -/
theorem compensator_mulLeft (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ}
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V)
    {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    compensator ν (G.mulLeft hGa hVm hVb).toFun T
      = fun ω => V ω ^ 2 * compensator ν G.toFun T ω := by
  funext ω
  change (∫ u in Set.Icc (0 : ℝ) T, ∫ e, (V ω * G.toFun ω u e) ^ 2 ∂ν ∂volume)
    = V ω ^ 2 * ∫ u in Set.Icc (0 : ℝ) T, ∫ e, (G.toFun ω u e) ^ 2 ∂ν ∂volume
  simp_rw [mul_pow, integral_const_mul]
/-- The weighted second moment of the compensated integral of an integrand vanishing up to
`a`, against a bounded weight measurable at `a`, is the weighted compensator. -/
theorem integral_mul_sq_integral (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ} (ha : 0 ≤ a)
    (haT : a ≤ T) (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ a] U) {M : ℝ} (hUb : ∀ ω, |U ω| ≤ M) :
    ∫ ω, U ω * (G.integral N hℱ ω) ^ 2 ∂P = ∫ ω, U ω * compensator ν G.toFun T ω ∂P :=
  integral_mul_sq_stochasticIntegral N hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global ha haT hGa hUm hUb
end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


