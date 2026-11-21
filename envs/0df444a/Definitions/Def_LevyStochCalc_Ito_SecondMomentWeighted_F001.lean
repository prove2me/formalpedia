-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F001
-- name    : LevyStochCalc_Ito_SecondMomentWeighted_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:00.825174+00:00
-- url     : https://prove2.me/theorems/def4b551-7ec7-4042-b1c4-21b7183cfe76
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentWeighted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentWeighted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F000
import Definitions.Def_SourceProof_fcc20476ce1053d13b71a947

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

/-- **The exponential weighting of an absolutely continuous function.** If
`m(s) = m₀ + ∫_0^s g` on `(0, T]` with `g` integrable on `[0, T]`, then
`e^{βT} m(T) = m₀ + ∫_0^T e^{βs} (β m(s) + g(s)) ds`. -/
theorem exp_mul_eq_add_setIntegral {m g : ℝ → ℝ} {m₀ T : ℝ} (hT : 0 < T)
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (hm : ∀ s ∈ Set.Ioc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r) (β : ℝ) :
    Real.exp (β * T) * m T
      = m₀ + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β * m s + g s) := by
  have hG : ContinuousOn (fun s => ∫ r in Set.Icc (0 : ℝ) s, g r) (Set.Icc (0 : ℝ) T) :=
    intervalIntegral.continuousOn_primitive_Icc hg
  have h1 : Integrable (fun s => β * Real.exp (β * s) * m₀)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s) * m₀).integrableOn_Icc
  have h2 : Integrable (fun s => β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ((by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).continuousOn.mul
      hG).integrableOn_Icc
  have h12 : Integrable (fun s => β * Real.exp (β * s) * m₀
      + β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := h1.add h2
  have h3 : Integrable (fun s => Real.exp (β * s) * g s)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    IntegrableOn.continuousOn_mul
      (by fun_prop : Continuous fun s : ℝ => Real.exp (β * s)).continuousOn hg isCompact_Icc
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Real.exp (β * s) * (β * m s + g s)
        = β * Real.exp (β * s) * m₀
          + β * Real.exp (β * s) * (∫ r in Set.Icc (0 : ℝ) s, g r)
          + Real.exp (β * s) * g s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hs0
    rw [hm s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩]
    ring
  have h0 : ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * m₀
      = (Real.exp (β * T) - 1) * m₀ := by
    rw [integral_mul_const, setIntegral_mul_exp_mul β hT.le, mul_zero, Real.exp_zero]
  rw [integral_congr_ae hae, integral_add h12 h3, integral_add h1 h2,
    _root_.Prove2MeSourceProof.h_fcc20476ce1053d13b71a947 hg β, hm T ⟨hT, le_rfl⟩, h0]
  ring
end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The squared norm of a diffusion coordinate is jointly measurable. -/
theorem measurable_uncurry_sq_diffusion
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2) :=
  (h.σ_meas j).nnnorm.coe_nnreal_ennreal.pow_const 2
/-- The jump energy density `(ω, s) ↦ ∫_E γ(ω, s, e)² ν(de)` is jointly measurable. -/
theorem measurable_uncurry_lintegral_sq_jump
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ) :
    Measurable (Function.uncurry fun ω s => ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
  ((h.γ_meas.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
      (ν := ν)
end Weighted

section WeightedVector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end AugmentedMore

end LevyStochCalc.Ito.SecondMoment


