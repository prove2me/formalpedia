-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
-- name    : LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:15:58.782278+00:00
-- url     : https://prove2.me/theorems/76c9ee64-cbc0-47a5-a04b-bcafc8633d9d
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaCutoffLocalise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaCutoffLocalise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
import Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increment formula for a translated path with no bound on the derivatives

The family of events on which a translated path stays in a ball over a bounded window exhausts
the sample space, and on the `m`-th member a twice continuously differentiable function agrees
with its box cutoff of radius `m + 1` along the translated path, together with its first two
derivatives. Transferring the increment formula for the cutoff along that family therefore gives
Itô's formula for the increment of the translated path between two ordered stopping times, with
no bound on the derivatives of the function and none on the translation; the stochastic terms
are matched there by hypothesis, from a stopping time below which the two integrands agree.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u

section Localise

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-- Two stopped increments whose integrands agree between the two stopping times and below a
third one have the same Itô integral on an event where that third time has not been reached. -/
theorem stochasticIntegralBrownian_stopped_sub_congr_of_mem
    (W : Brownian.BrownianMotion P) (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : Brownian.IsBrownianFiltration W ℱ')
    {σ τ ρ : Ω → WithTop ℝ} (hρ : MeasureTheory.IsStoppingTime ℱ' ρ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s)
    (hq₁ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ A ω s - Probability.stopped σ A ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s)
    (hq₂ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ B ω s - Probability.stopped σ B ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ ρ ω →
      σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s)
    {T : ℝ} (hT : 0 < T) {Sset : Set Ω}
    (hS : ∀ ω ∈ Sset, ((T : ℝ) : WithTop ℝ) ≤ ρ ω) :
    ∀ᵐ ω ∂P, ω ∈ Sset →
      stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ A ω s - Probability.stopped σ A ω s)
          hm₁ hp₁ hq₁ T ω
        = stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ B ω s - Probability.stopped σ B ω s)
          hm₂ hp₂ hq₂ T ω := by
  have h := _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966 ρ W ℱ' hℱ hρ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (fun ω s hs hle => stopped_sub_congr hστ fun h1 h2 => hagree ω s hs hle h1 h2) hT
  filter_upwards [h] with ω hω hmem
  exact hω (hS ω hmem)
end Localise

end LevyStochCalc.Ito.JumpFormulaCutoff


