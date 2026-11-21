-- Prove2me | Definitions.Def_SourceProof_0122a571e95691a0e466a41c
-- name    : SourceProof_0122a571e95691a0e466a41c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:27:00.739826+00:00
-- url     : https://prove2.me/theorems/b8904e66-67fb-45da-bca4-ddcff1e5f3ef
-- title:
--   LevyStochCalc source module: SourceProof_0122a571e95691a0e466a41c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.memLp_two_of_isItoLevyProcess` comes from the `LevyStochCalc.Ito.SecondMomentQuadratic` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F002
import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end PolarisedMarked

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}


theorem _root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (X t) 2 P := by
  have hS2 : ∀ j : Fin d, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t) 2 P := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : MemLp (fun ω => ∑ j, LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t ω) 2 P :=
    memLp_finsetSum Finset.univ fun j _ => hS2 j
  have hC2 : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hDr2 : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω) 2 P :=
    LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht
      (LevyStochCalc.Ito.SecondMoment.energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht)
  refine (((hX₀2.add hDr2).add hSsum2).add hC2).ae_eq ?_
  exact Filter.EventuallyEq.symm (h.decomposition t ht)
end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Augmented

end LevyStochCalc.Ito.SecondMoment


