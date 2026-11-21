-- Prove2me | Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002
-- name    : LevyStochCalc_Ito_StabilityEstimate_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:41:04.070444+00:00
-- url     : https://prove2.me/theorems/288e1750-49d7-4c1d-ba05-fb95b8b2ccd4
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.StabilityEstimate
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.StabilityEstimate in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_SecondMomentQuadratic_F000
import Definitions.Def_SourceProof_0122a571e95691a0e466a41c
import Definitions.Def_SourceProof_5f001695308f2960cc01c3ca
import Definitions.Def_SourceProof_700488d66fa58fc241f21293
import Definitions.Def_SourceProof_c881239cef4c0ad2e7f9696d
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

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

/-- **Uniqueness from the stability estimate.** Two Itô–Lévy processes over the same driver whose
coefficients satisfy the one-sided Lipschitz bounds and whose initial values agree almost surely
agree almost surely at every horizon. -/
theorem ae_eq_of_lipschitz_of_ae_eq_initial
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
    {L : ℝ}
    (hbLip : ∀ s ω, (X s ω - Y s ω) * (b s ω - b' s ω)
      ≤ L * ((X s ω - Y s ω) * (X s ω - Y s ω)))
    (hσLip : ∀ s ω, (∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hγLip : ∀ s ω, (∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hinit : X₀ =ᵐ[P] Y₀) {T : ℝ} (hT : 0 < T) :
    X T =ᵐ[P] Y T := by
  have hbound := _root_.Prove2MeSourceProof.h_c881239cef4c0ad2e7f9696d h h' 𝒲 hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2
    hb'm hb'p hb'q hbLip hσLip hγLip hT
  have hzero : ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hinit] with ω hω
    simp [hω]
  rw [hzero, mul_zero] at hbound
  have hΔ := _root_.Prove2MeSourceProof.h_5f001695308f2960cc01c3ca h h' hbm hb'm hbq hb'q
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  have hT2 : MemLp (fun ω => X T ω - Y T ω) 2 P :=
    _root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c hΔ (hX₀2.sub hY₀2) hΔbm hΔbq hT.le
  have hTi : Integrable (fun ω => (X T ω - Y T ω) * (X T ω - Y T ω)) P :=
    hT2.integrable_mul hT2
  have hTnn : 0 ≤ᵐ[P] fun ω => (X T ω - Y T ω) * (X T ω - Y T ω) :=
    Eventually.of_forall fun ω => mul_self_nonneg _
  have hTz : ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P = 0 :=
    le_antisymm hbound (integral_nonneg fun ω => mul_self_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg_ae hTnn hTi).mp hTz
  filter_upwards [this] with ω hω
  have : (X T ω - Y T ω) * (X T ω - Y T ω) = 0 := hω
  have hz : X T ω - Y T ω = 0 := by
    exact mul_self_eq_zero.mp this
  linarith
end Stability

end LevyStochCalc.Ito.Stability


