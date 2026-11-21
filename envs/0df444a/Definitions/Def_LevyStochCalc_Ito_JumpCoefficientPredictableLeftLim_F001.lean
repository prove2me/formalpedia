-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
-- name    : LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:09:44.334392+00:00
-- url     : https://prove2.me/theorems/8aa7859e-2f94-4c27-8f9b-541e0d132472
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000
import Definitions.Def_SourceProof_c5cf45bd11a3d53a89dd04c6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump coefficient read at the left limits of the path

The left limits of a path are the limit along a dyadic grid of the path itself, so for a path
having left limits at the positive times they are known at the current time whenever the path is
adapted and they are left-continuous there; cut to the positive times they are predictable, hence
the jump coefficient of a jump diffusion evaluated at them is predictable on the time–mark space.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- **The jump coefficient of a jump diffusion, evaluated at the left limits of the path, is
predictable on the time–mark space.** -/
theorem markedPredictable_jumpCoeff_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (i : Fin n)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i)
    (hγ0 : ∀ s : ℝ, s ≤ 0 → ∀ (x : Fin n → ℝ) (e : E), coeffs.γ s x e i = 0) :
    MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i := by
  classical
  have h := _root_.Prove2MeSourceProof.h_a284e225504f48706843f4e8 (ν := ν)
    (_root_.Prove2MeSourceProof.h_c5cf45bd11a3d53a89dd04c6 X ℱ hXadapt hleft)
    (f := fun s x e => coeffs.γ s x e i) hγ
  have hrw : (fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then coeffs.γ s (leftLimPathPos X s ω) e i else 0)
      = fun (ω : Ω) (s : ℝ) (e : E) => coeffs.γ s (leftLimPath X s ω) e i := by
    funext ω s e
    by_cases hs : 0 < s
    · simp only [if_pos hs, leftLimPathPos]
    · rw [if_neg hs, hγ0 s (not_lt.mp hs)]
  rwa [hrw] at h
/-- **The jump coefficients of a regular jump-diffusion coefficient bundle, evaluated at the left
limits of the path, are predictable on the time–mark space.** -/
theorem markedPredictable_forall_jumpCoeff_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hreg : coeffs.IsRegular ν)
    (hγ0 : ∀ s : ℝ, s ≤ 0 → ∀ (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0) :
    ∀ i : Fin n, MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i :=
  fun i => markedPredictable_jumpCoeff_leftLimPath X ℱ i hXadapt hleft
    ((measurable_pi_apply i).comp hreg.2.2.1)
    (fun s hs x e => by rw [hγ0 s hs x e]; rfl)
end LevyStochCalc.Ito.JumpSplitting


