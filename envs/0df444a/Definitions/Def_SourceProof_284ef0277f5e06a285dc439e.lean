-- Prove2me | Definitions.Def_SourceProof_284ef0277f5e06a285dc439e
-- name    : SourceProof_284ef0277f5e06a285dc439e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:15.246616+00:00
-- url     : https://prove2.me/theorems/b9f2e599-795f-4627-a2ee-1bcc2e39342a
-- title:
--   LevyStochCalc source module: SourceProof_284ef0277f5e06a285dc439e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.vectorItoProcess_zero_ae` comes from the `LevyStochCalc.Brownian.VectorItoStopped` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in

theorem _root_.Prove2MeSourceProof.h_284ef0277f5e06a285dc439e
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift 0 =ᵐ[P] X₀ := by
  have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k) (hHs p k) 0 ω
        = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) le_rfl
  filter_upwards [hall] with ω hz
  funext p
  have hdrift : ∫ s in Set.Icc (0 : ℝ) 0, bdrift p ω s ∂volume = 0 := by
    rw [show Set.Icc (0 : ℝ) 0 = {(0 : ℝ)} from Set.Icc_self 0,
      MeasureTheory.setIntegral_measure_zero _ Real.volume_singleton]
  simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, vectorItoMartingale, coordItoIntegral, hdrift]
  have hsum : ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) 0 ω = 0 :=
    Finset.sum_eq_zero fun k _ => hz p k
  rw [hsum]
  ring
end StoppedVersion

end LevyStochCalc.Brownian.Ito


