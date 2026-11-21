-- Prove2me | Definitions.Def_SourceProof_5f001695308f2960cc01c3ca
-- name    : SourceProof_5f001695308f2960cc01c3ca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:37:34.81589+00:00
-- url     : https://prove2.me/theorems/2e525835-2aa7-41b0-8349-40d5eb056421
-- title:
--   LevyStochCalc source module: SourceProof_5f001695308f2960cc01c3ca
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Stability.isItoLevyProcess_sub` comes from the `LevyStochCalc.Ito.StabilityEstimate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_SourceProof_388a40baa407d0b0ae15b23c
import Definitions.Def_SourceProof_426ff55101b7b0df983e6be6
import Definitions.Def_SourceProof_6cdc47526d2ae213604fd2f4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Algebra.Order.Floor

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


theorem _root_.Prove2MeSourceProof.h_5f001695308f2960cc01c3ca
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN
      (fun t ω => X t ω - Y t ω) (fun ω => X₀ ω - Y₀ ω) (fun s ω => b s ω - b' s ω)
      (fun s ω j => σ s ω j - σ' s ω j) (fun ω s e => γ ω s e - γ' ω s e) := by
  classical
  -- the admissibility of the differenced data, in the shape the integrals expect
  have hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j - σ' s ω j) :=
    fun j => (h.σ_meas j).sub (h'.σ_meas j)
  have hσp : ∀ j : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => σ s ω j - σ' s ω j := fun j => (h.σ_prog j).sub (h'.σ_prog j)
  have hσq : ∀ (j : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
    _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _)
      (h.σ_meas j) (h'.σ_meas j) (h.σ_sq j) (h'.σ_sq j)
  have hγm : Measurable fun p : Ω × ℝ × E => γ p.1 p.2.1 p.2.2 - γ' p.1 p.2.1 p.2.2 :=
    h.γ_meas.sub h'.γ_meas
  have hγp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => γ ω s e - γ' ω s e :=
    LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_sub h.γ_prog h'.γ_prog
  have hγq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T hT =>
    _root_.Prove2MeSourceProof.h_388a40baa407d0b0ae15b23c h.γ_meas h'.γ_meas (h.γ_sq T hT) (h'.γ_sq T hT)
  refine
    { measurable_path := h.measurable_path.sub h'.measurable_path
      σ_meas := hσm
      σ_prog := hσp
      σ_sq := hσq
      γ_meas := hγm
      γ_prog := hγp
      γ_sq := hγq
      decomposition := ?_ }
  intro t ht
  -- the Brownian coordinates subtract
  have hB : ∀ j : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
          (fun ω s => σ s ω j - σ' s ω j) (hσm j) (hσp j) (hσq j) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
            (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
              (fun ω s => σ' s ω j) (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) t ω := by
    intro j
    rcases eq_or_lt_of_le ht with h0 | hpos
    · have ht0 : t ≤ 0 := le_of_eq h0.symm
      filter_upwards [_root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97
          (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j - σ' s ω j) (hσm j) (hσp j) (hσq j) ht0,
        _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97
          (D.W.W j) ℱ (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) ht0,
        _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97
          (D.W.W j) ℱ (hℱW j) _ (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) ht0] with ω e0 e1 e2
      simp only [Pi.zero_apply] at e0 e1 e2
      rw [e0, e1, e2]
      ring
    · exact _root_.Prove2MeSourceProof.h_426ff55101b7b0df983e6be6 (D.W.W j) ℱ (hℱW j)
        (h.σ_meas j) (h'.σ_meas j) (h.σ_prog j) (h'.σ_prog j) (h.σ_sq j) (h'.σ_sq j)
        (hσm j) (hσp j) (hσq j) hpos
  -- the compensated integrals subtract
  have hC : ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
          (fun ω s e => γ ω s e - γ' ω s e) hγm hγp hγq t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog
            h.γ_sq t ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ' h'.γ_meas
              h'.γ_prog h'.γ_sq t ω := by
    rcases eq_or_lt_of_le ht with h0 | hpos
    · have ht0 : t ≤ 0 := le_of_eq h0.symm
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
          D.N hℱN hγm hγp hγq ht0,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N hℱN
          h.γ_meas h.γ_prog h.γ_sq ht0,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N hℱN
          h'.γ_meas h'.γ_prog h'.γ_sq ht0] with ω e0 e1 e2
      simp only [Pi.zero_apply] at e0 e1 e2
      rw [e0, e1, e2]
      ring
    · exact _root_.Prove2MeSourceProof.h_6cdc47526d2ae213604fd2f4 D.N hℱN h.γ_meas
        h'.γ_meas h.γ_prog h'.γ_prog h.γ_sq h'.γ_sq hγm hγp hγq hpos
  -- the drift integrals subtract
  have hb : ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) t, (b s ω - b' s ω)
      = (∫ s in Set.Icc (0 : ℝ) t, b s ω) - ∫ s in Set.Icc (0 : ℝ) t, b' s ω := by
    filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq,
      LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b' s ω) hb'm hb'q] with ω hω hω'
    exact integral_sub (hω t) (hω' t)
  filter_upwards [h.decomposition t ht, h'.decomposition t ht, hC, hb,
    (ae_all_iff.mpr hB)] with ω e1 e2 e3 e4 e5
  simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
    LevyStochCalc.Brownian.Ito.stochasticIntegral] at e1 e2 ⊢
  rw [e1, e2, e3, e4, Finset.sum_congr rfl fun j _ => e5 j, Finset.sum_sub_distrib]
  ring
end Difference

section Stability

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

end Stability

end LevyStochCalc.Ito.Stability


