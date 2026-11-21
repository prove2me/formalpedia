-- Prove2me | Definitions.Def_SourceProof_d8b446e22164b7620e52d72e
-- name    : SourceProof_d8b446e22164b7620e52d72e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:50:10.891969+00:00
-- url     : https://prove2.me/theorems/73206b40-ff24-431d-8e8f-92866ef945a2
-- title:
--   LevyStochCalc source module: SourceProof_d8b446e22164b7620e52d72e
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integrableOn_integral_mul_drift` comes from the `LevyStochCalc.Ito.SecondMomentWeighted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F001
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_SourceProof_20d586a8e09491862e290520
import Definitions.Def_SourceProof_b4f6afa5f19da9f228b3652e

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

end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_d8b446e22164b7620e52d72e
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, X s ω * b s ω ∂P) (Set.Icc (0 : ℝ) T) := by
  classical
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  have hS2 : ∀ j, MemLp (S j T) 2 P := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) T
  have hC2 : MemLp (C T) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq T
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hXb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * (∫ r in Set.Icc (0 : ℝ) s, b r ω) ∂P
        + (∑ j, ∫ ω, b s ω * S j T ω ∂P) + ∫ ω, b s ω * C T ω ∂P := by
    filter_upwards [LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT), hsw] with s hs2 hs
    exact _root_.Prove2MeSourceProof.h_b4f6afa5f19da9f228b3652e h hX₀2 hbm hbq hs.1 hs.2 (hbp.stronglyMeasurable_eval s) hs2
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst hg)).integral_prod_right
  have hint_Dr : Integrable (fun s => ∫ ω, b s ω * (∫ r in Set.Icc (0 : ℝ) s, b r ω) ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ ω, b s ω * LevyStochCalc.Ito.SecondMoment.running b T (ω, s) ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ((LevyStochCalc.Ito.SecondMoment.memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
        (_root_.Prove2MeSourceProof.h_20d586a8e09491862e290520 (P := P) hbm (hbq T hT))).integral_prod_right
    refine h1.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (LevyStochCalc.Ito.SecondMoment.running_eq hs)
  have i3 : Integrable (fun s => ∑ j, ∫ ω, b s ω * S j T ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => hint_s _ (hS2 j)
  refine ((((hint_s X₀ hX₀2).add hint_Dr).add i3).add (hint_s _ hC2)).congr ?_
  filter_upwards [hXb] with s hs
  exact hs.symm
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


