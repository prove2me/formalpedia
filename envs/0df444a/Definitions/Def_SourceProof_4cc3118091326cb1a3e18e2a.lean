-- Prove2me | Definitions.Def_SourceProof_4cc3118091326cb1a3e18e2a
-- name    : SourceProof_4cc3118091326cb1a3e18e2a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:42:35.753297+00:00
-- url     : https://prove2.me/theorems/e039bf81-e043-4489-a702-77330783b032
-- title:
--   LevyStochCalc source module: SourceProof_4cc3118091326cb1a3e18e2a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.stochasticIntegralBrownian_sum_univ` comes from the `LevyStochCalc.Ito.FiniteActivityMixed` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F001
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F002
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity Itô–Lévy identity along a truncated path, in the mixed form

Along a càdlàg path `y` that is a continuous vector Itô process plus the left-limit jump sum of
a jump diffusion `X` over a mark set of finite intensity, the increment of a `C²` state function
with bounded derivatives is the mixed drift integral, the Brownian integral of the mixed
diffusion integrand, the compensated integral of the mixed jump increment over the mark set and
the compensator-drift integral over that set. The derivatives of the state function are read
along `y` and the coefficients along `X`.

The proof telescopes Itô's formula for the time-augmented continuous part between consecutive
arrival times of the mark set, identifies the increments across the arrival times with the
atom sum of the mixed jump increment read at the left limits, and identifies that atom sum with
the pathwise form of the compensated integral.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section BrownianSum

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_4cc3118091326cb1a3e18e2a {T : ℝ} (hT : 0 < T) : ∀ {m : ℕ}
    (H : Fin m → Ω → ℝ → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : Fin m) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => ∑ i, H i ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i, H i ω s)
    (hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖∑ i, H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => ∑ i, H i ω s) hms hps hqs T
      =ᵐ[P] fun ω => ∑ i, stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  intro m
  induction m with
  | zero =>
    intro H hm hp hq hms hps hqs
    have h0 : (fun ω s => ∑ i : Fin 0, H i ω s) = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω s
      simp
    have hm0 : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := measurable_const
    have hp0 : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      LevyStochCalc.Probability.progressivelyMeasurable_const ℱ 0
    have hq0 : ∀ T : ℝ, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T _
      simp
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ h0 hms hps hqs hm0 hp0 hq0 T]
    filter_upwards [_root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 W ℱ hℱ hm0 hp0 hq0 T] with ω hω
    rw [hω]
    simp
  | succ m ih =>
    intro H hm hp hq hms hps hqs
    have hsucc : (fun ω s => ∑ i : Fin (m + 1), H i ω s)
        = fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s := by
      funext ω s
      exact Fin.sum_univ_succ _
    have hmt : Measurable (Function.uncurry fun ω s => ∑ i : Fin m, H i.succ ω s) :=
      Finset.measurable_sum _ fun i _ => hm i.succ
    have hpt : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i : Fin m, H i.succ ω s :=
      LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_finset_sum _ fun i _ => hp i.succ
    have hqt : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∑ i : Fin m, H i.succ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T hT =>
      LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le (a := fun i => H i.succ) (c := 1)
        (fun i => hm i.succ) (fun ω s => by rw [one_mul]; exact Finset.abs_sum_le_sum_abs _ _) T
        (fun i => hq i.succ T hT)
    have hma : Measurable (Function.uncurry fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s) :=
      (hm 0).add hmt
    have hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s := (hp 0).add hpt
    have hqa : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H 0 ω s + ∑ i : Fin m, H i.succ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hqs T hT
      simp only [Fin.sum_univ_succ] at this
      exact this
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hsucc hms hps hqs hma hpa hqa T]
    filter_upwards [_root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 W ℱ hℱ (hm 0) hmt (hp 0) hpt (hq 0) hqt hma
      hpa hqa hT, ih (fun i => H i.succ) (fun i => hm i.succ)
      (fun i => hp i.succ) (fun i => hq i.succ) hmt hpt hqt] with ω h1 h2
    rw [h1, h2, Fin.sum_univ_succ]
end BrownianSum

section Main

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Main

end LevyStochCalc.Ito.JumpFormula


