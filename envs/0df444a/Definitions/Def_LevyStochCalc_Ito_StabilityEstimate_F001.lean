-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
-- name    : LevyStochCalc_Ito_StabilityEstimate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:03:51.294898+00:00
-- url     : https://prove2.me/theorems/aa0a0c93-02ee-4748-acf5-e2a42ca61940
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.StabilityEstimate
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.StabilityEstimate in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F000
import Definitions.Def_SourceProof_5f001695308f2960cc01c3ca
import Definitions.Def_SourceProof_700488d66fa58fc241f21293

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted stability estimates for Itô–Lévy processes

The difference of two Itô–Lévy processes over the same Lévy driver and filtration is again an
Itô–Lévy process, with the differenced data (`isItoLevyProcess_sub`). Feeding it to the
exponentially weighted second-moment identity turns a bound on the rate

`2 𝔼[ΔX_s Δb_s] + ∑_j 𝔼[|Δσ_j(s)|²] + 𝔼 ∫_E |Δγ(s, e)|² ν(de) ≤ c 𝔼[|ΔX_s|²]`

into the stability estimate `𝔼[|ΔX_T|²] ≤ e^{cT} 𝔼[|ΔX₀|²]`, with no Grönwall lemma: the
exponential weight does the work. A drift, diffusion and jump coefficient Lipschitz in the state
gives such a rate bound with `c = 2L + 2L²`, and equal initial values then force the two
processes to agree at the horizon.

## Main statements

* `integral_mul_self_le_of_rate_le` — the weighted identity as a bound: a rate bounded by
  `c 𝔼[X_s²]` at almost every time of the window gives `𝔼[X_T²] ≤ e^{cT} 𝔼[X₀²]`.
* `isItoLevyProcess_sub` — the difference of two Itô–Lévy processes over the same driver is an
  Itô–Lévy process with the differenced initial value, drift, diffusion and jump coefficient.
* `integral_sub_mul_self_le_of_rate_le` — the stability estimate under a rate bound on the
  difference.
* `integral_sub_mul_self_le_of_lipschitz` — the stability estimate under pointwise Lipschitz
  bounds on the differences of the coefficients, with `c = 2L + 2L²`.
* `ae_eq_of_lipschitz_of_ae_eq_initial` — two Itô–Lévy processes with Lipschitz-close
  coefficients and almost surely equal initial values agree almost surely at every horizon.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Stability

open LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section RateBound

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end RateBound

section Difference

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

variable {d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

end Difference

section Stability

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- A lintegral dominated by the `ℝ≥0∞` image of an integrable nonnegative function is finite,
and its real value is at most that function's integral. -/
theorem toReal_lintegral_le_of_le {f : Ω → ℝ≥0∞} {g : Ω → ℝ} (hgi : Integrable g P)
    (hg0 : ∀ ω, 0 ≤ g ω) (hle : ∀ ω, f ω ≤ ENNReal.ofReal (g ω)) :
    (∫⁻ ω, f ω ∂P).toReal ≤ ∫ ω, g ω ∂P ∧ ∫⁻ ω, f ω ∂P ≠ ⊤ := by
  have hkey : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (∫ ω, g ω ∂P) := by
    calc ∫⁻ ω, f ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := lintegral_mono hle
      _ = ENNReal.ofReal (∫ ω, g ω ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)).symm
  refine ⟨?_, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkey⟩
  calc (∫⁻ ω, f ω ∂P).toReal
      ≤ (ENNReal.ofReal (∫ ω, g ω ∂P)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
    _ = ∫ ω, g ω ∂P := ENNReal.toReal_ofReal (integral_nonneg hg0)
/-- **The stability estimate for two Itô–Lévy processes under a rate bound.** If at almost every
time of the window the rate of the difference is at most `c` times its second moment, the second
moment of the difference at the horizon is at most `e^{cT}` times its initial value. -/
theorem integral_sub_mul_self_le_of_rate_le
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {c T : ℝ} (hT : 0 < T)
    (hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        ≤ c * ∫ ω, (X s ω - Y s ω) * (X s ω - Y s ω) ∂P) :
    ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P
      ≤ Real.exp (c * T) * ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P := by
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω - b' s ω :=
    hbp.sub hb'p
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  exact integral_mul_self_le_of_rate_le (_root_.Prove2MeSourceProof.h_5f001695308f2960cc01c3ca h h' hbm hb'm hbq hb'q) 𝒲
    (hX₀.sub hY₀) (hX₀2.sub hY₀2) hΔbm hΔbp hΔbq hT hrate
end Stability

end LevyStochCalc.Ito.Stability


