-- Prove2me | Definitions.Def_SourceProof_78ebf7438df184d60f260ac5
-- name    : SourceProof_78ebf7438df184d60f260ac5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:55:14.320541+00:00
-- url     : https://prove2.me/theorems/e85817fc-5e6e-4841-89ae-a909eaeb7951
-- title:
--   LevyStochCalc source module: SourceProof_78ebf7438df184d60f260ac5
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.hitInd_mul_stochasticIntegral_indIoc` comes from the `LevyStochCalc.Ito.CompensatedLocalityWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_SourceProof_f2734a4bc0d51d1dd6733e48

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_78ebf7438df184d60f260ac5 {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    {c t : ℝ} (hc : 0 ≤ c) (hct : c < t)
    (hmV : Measurable fun p : Ω × ℝ × E =>
      hitInd τ c p.1 * (indIoc Ω c t p.1 p.2.1 * φ p.1 p.2.1 p.2.2))
    (hpV : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e))
    (hqV : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e)‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤) :
    stochasticIntegral N ℱ hℱ (fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e))
        hmV hpV hqV t
      =ᵐ[P] fun ω => hitInd τ c ω
        * stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω c t ω s * φ ω s e)
          (measurable_indIoc_mul hm c t) (markedProgressivelyMeasurable_indIoc_mul hp c t)
          (sq_int_global_indIoc_mul hq c t) t ω := by
  have ht : 0 < t := hc.trans_lt hct
  let G : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ t :=
    { toFun := fun ω s e => LevyStochCalc.Brownian.Ito.indIoc Ω c t ω s * φ ω s e
      measurable_uncurry := LevyStochCalc.Poisson.Compensated.measurable_indIoc_mul hm c t
      progressive := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hp c t
      vanishing := fun ω s e hs => by
        have : s ∉ Set.Ioc c t := fun h => hs ⟨hc.trans h.1.le, h.2⟩
        simp [LevyStochCalc.Brownian.Ito.indIoc, this]
      energy_ne_top := (LevyStochCalc.Poisson.Compensated.sq_int_global_indIoc_mul hq c t t ht).ne }
  have hGa : ∀ ω s e, s ≤ c → G.toFun ω s e = 0 := fun ω s e hs => by
    have : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr hs)
    simp [G, LevyStochCalc.Brownian.Ito.indIoc, this]
  exact _root_.Prove2MeSourceProof.h_f2734a4bc0d51d1dd6733e48 N hℱ ht G hc hct.le hGa
    (LevyStochCalc.Brownian.Ito.stronglyMeasurable_hitInd τ hτ c) (LevyStochCalc.Brownian.Ito.abs_hitInd_le_one τ c)
end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Linear

end LevyStochCalc.Poisson.Compensated


