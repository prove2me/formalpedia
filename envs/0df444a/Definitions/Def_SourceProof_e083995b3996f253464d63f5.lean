-- Prove2me | Definitions.Def_SourceProof_e083995b3996f253464d63f5
-- name    : SourceProof_e083995b3996f253464d63f5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:59:53.326822+00:00
-- url     : https://prove2.me/theorems/9096dbd2-084d-42a9-92b4-ff675ce2cf02
-- title:
--   LevyStochCalc source module: SourceProof_e083995b3996f253464d63f5
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markedStopped_eq_sub_sum` comes from the `LevyStochCalc.Ito.CompensatedLocalityStopping` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Optional stopping and locality of the compensated integral

On the window `(0, t]` the integrand cut off at a stopping time of finite range is the integrand
minus, for each value the stopping time takes before `t`, the piece it carries after that value,
so its integral is the integral minus the corresponding increments; a general stopping time is
the decreasing limit of its grid approximations, whose cut-off integrands converge in energy, and
the difference isometry squeezes the integrals, so two marked integrands agreeing up to — or
strictly before — a stopping time have the same compensated integral at every time the stopping
time has not reached.

## Main definitions

* `markedCutTerm τ φ c t` — the piece of `φ` on `(c, t]` that the cut at `τ = c` removes.

## Main statements

* `stochasticIntegral_markedStopped_finiteRange` — optional stopping at a stopping time of
  finite range.
* `stochasticIntegral_markedStopped_eq_of_le` — at a time the stopping time has not reached,
  cutting the integrand off at it changes nothing.
* `stochasticIntegral_congr_of_le`, `stochasticIntegral_congr_of_lt` — integrands agreeing up
  to (respectively, strictly before) a stopping time have the same integral at every time the
  stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one hitInd abs_hitInd_le_one measurable_hitInd
  stronglyMeasurable_hitInd gridStop gridPt isStoppingTime_gridStop le_gridStop gridPt_nonneg
  gridPt_lt_of_lt gridStop_finiteRange sq_nnnorm_sub_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section FiniteRange

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_e083995b3996f253464d63f5 {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    (fun ω s e => indIoc Ω 0 t ω s * markedStopped τ φ ω s e)
      = fun ω s e => indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, markedCutTerm τ φ c t ω s e := by
  classical
  funext ω s e
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
  · have hind0 : LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s = 1 := by simp [LevyStochCalc.Brownian.Ito.indIoc, hs]
    have hzero : ∀ c ∈ J, τ ω ≠ ((c : ℝ) : WithTop ℝ) →
        LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e = 0 := by
      intro c _ hne
      simp [LevyStochCalc.Poisson.Compensated.markedCutTerm, LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ((c : ℝ) :
        WithTop ℝ)} from hne)]
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | hge
    · have hsum : ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e
          = LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c₀ t ω s e := by
        refine Finset.sum_eq_single_of_mem c₀ hc₀J fun c hc hne => ?_
        refine hzero c hc ?_
        rw [hc₀]
        exact fun hcc => hne (by exact_mod_cast hcc.symm)
      have hhit : LevyStochCalc.Brownian.Ito.hitInd τ c₀ ω = 1 := by
        simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((c₀ : ℝ) : WithTop ℝ)}
          from hc₀)]
      rw [hsum, hind0, LevyStochCalc.Poisson.Compensated.markedCutTerm, hhit]
      by_cases hsc : s ≤ c₀
      · have h1 : LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e = φ ω s e := by
          rw [LevyStochCalc.Poisson.Compensated.markedStopped, if_pos]
          rw [hc₀]
          exact_mod_cast hsc
        have h2 : LevyStochCalc.Brownian.Ito.indIoc Ω c₀ t ω s = 0 := by
          simp only [LevyStochCalc.Brownian.Ito.indIoc]
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr hsc)
        rw [h1, h2]
        ring
      · rw [not_le] at hsc
        have h1 : LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e = 0 := by
          rw [LevyStochCalc.Poisson.Compensated.markedStopped, if_neg]
          rw [hc₀]
          exact fun hcon => absurd (by exact_mod_cast hcon : s ≤ c₀) (not_le.mpr hsc)
        have h2 : LevyStochCalc.Brownian.Ito.indIoc Ω c₀ t ω s = 1 := by
          simp [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_mem (show s ∈ Set.Ioc c₀ t from ⟨hsc, hs.2⟩)]
        rw [h1, h2]
        ring
    · have hsum : ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e = 0 := by
        refine Finset.sum_eq_zero fun c hc => hzero c hc ?_
        intro hcon
        rw [hcon] at hge
        exact absurd (by exact_mod_cast hge : t ≤ c) (not_le.mpr (hJt c hc))
      have h1 : LevyStochCalc.Poisson.Compensated.markedStopped τ φ ω s e = φ ω s e := by
        rw [LevyStochCalc.Poisson.Compensated.markedStopped, if_pos]
        exact le_trans (by exact_mod_cast hs.2) hge
      rw [hsum, hind0, h1]
      ring
  · have hind0 : LevyStochCalc.Brownian.Ito.indIoc Ω 0 t ω s = 0 := by
      simp only [LevyStochCalc.Brownian.Ito.indIoc]
      exact Set.indicator_of_notMem hs _
    have hsum : ∑ c ∈ J, LevyStochCalc.Poisson.Compensated.markedCutTerm τ φ c t ω s e = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hnot : s ∉ Set.Ioc c t := fun hmem =>
        hs ⟨lt_of_le_of_lt (hJ0 c hc) hmem.1, hmem.2⟩
      have hz : LevyStochCalc.Brownian.Ito.indIoc Ω c t ω s = 0 := by
        simp only [LevyStochCalc.Brownian.Ito.indIoc]
        exact Set.indicator_of_notMem hnot _
      simp [LevyStochCalc.Poisson.Compensated.markedCutTerm, hz]
    rw [hsum, hind0]
    ring
variable {τ φ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end FiniteRange

section Local

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {τ : Ω → WithTop ℝ}
  {φ : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Local

end LevyStochCalc.Poisson.Compensated


