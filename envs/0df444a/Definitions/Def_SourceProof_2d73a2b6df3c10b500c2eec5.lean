-- Prove2me | Definitions.Def_SourceProof_2d73a2b6df3c10b500c2eec5
-- name    : SourceProof_2d73a2b6df3c10b500c2eec5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:54.392382+00:00
-- url     : https://prove2.me/theorems/d2badc47-1559-411e-a59f-d0ffcf43e2ee
-- title:
--   LevyStochCalc source module: SourceProof_2d73a2b6df3c10b500c2eec5
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum` comes from the `LevyStochCalc.Ito.JumpSumIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F000
import Definitions.Def_SourceProof_07135226a3b6eb1d82b734e1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump sum of a finite-activity window

On a window `(0, T] × A` of finite intensity a Poisson random measure is almost surely a finite
sum of Dirac masses. Integer-valuedness makes each of those masses a natural number and
time-simplicity caps it at one, so the integral of a function against the random measure over the
window is the plain sum of the function's values over a finite set of window points carrying
pairwise distinct times. Those times are exactly the arrival times of the mark set inside the
window, so the sum is indexed by the strictly monotone enumeration of the arrival times, each
paired with the unique mark carried at that time.

Chaining that identity with `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise`
writes the jump sum of a predictable integrand `φ` as the Itô–Lévy integral of `φ` plus the
integral of `φ` itself against the reference intensity. That second term is not the compensator
drift of the Itô–Lévy formula: the latter integrates `u (x + γ e) - u x - ∑ i, γ i e * ∂ i u x`,
which differs from `φ = u (x + γ e) - u x` by the first-order term `∑ i, γ i e * ∂ i u x`.

## Main statements

* `LevyStochCalc.Poisson.exists_atomFinset_integral_eq_sum` — the integral over a window whose
  restricted measure is integer-valued and time-simple is a plain finite sum over window points.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum` — almost surely that sum is indexed
  by the strictly monotone enumeration of the arrival times in the window.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_sum_eq_stochasticIntegral_add` — almost surely the
  jump sum of a predictable integrand is its Itô–Lévy integral plus its integral against the
  reference intensity.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.4.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section AtomMass

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomMass

section AtomFinset

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomFinset

section Enumeration

end Enumeration

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)


theorem _root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ (k : ℕ) (θ : Fin k → ℝ) (ε : Fin k → E), StrictMono θ ∧
      Set.range θ = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} ∧
      (∀ i, θ i ∈ Set.Ioc (0 : ℝ) T ∧ ε i ∈ A) ∧
      ∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ i : Fin k, g (θ i, ε i) := by
  have hB : MeasurableSet (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν (T + 1)
  filter_upwards [LevyStochCalc.Poisson.ae_exists_finset_integral_eq_sum_Ioc N hA hAν T,
    _root_.Prove2MeSourceProof.h_2d4c8b457cb0b7f5fdc2dc58 N hB hfin, _root_.Prove2MeSourceProof.h_07135226a3b6eb1d82b734e1 N hB hfin]
    with ω hω hint hsimple
  obtain ⟨s, hlint, hbochner, -⟩ := hω
  obtain ⟨t, htW, htinj, htimes, htsum⟩ :=
    LevyStochCalc.Poisson.exists_atomFinset_integral_eq_sum N A hA hlint hbochner hint hsimple
  obtain ⟨k, θ, ε, hmono, hrange, hmem, hsum⟩ := LevyStochCalc.Poisson.exists_strictMono_enum_of_fst_inj t htinj
  refine ⟨k, θ, ε, hmono, by rw [hrange, htimes], fun i => ?_, fun g => ?_⟩
  · exact Set.mem_prod.mp (htW _ (hmem i))
  · rw [htsum g, hsum g]
end AlmostEverywhere

section Compensated

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Compensated

end LevyStochCalc.Poisson


