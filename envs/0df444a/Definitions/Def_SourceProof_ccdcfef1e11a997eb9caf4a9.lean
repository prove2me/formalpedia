-- Prove2me | Definitions.Def_SourceProof_ccdcfef1e11a997eb9caf4a9
-- name    : SourceProof_ccdcfef1e11a997eb9caf4a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:35:02.842733+00:00
-- url     : https://prove2.me/theorems/eae16b11-cabb-4eae-ad74-37f1b9ad6c1e
-- title:
--   LevyStochCalc source module: SourceProof_ccdcfef1e11a997eb9caf4a9
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.martingale_simpleIntegral_compensated` comes from the `LevyStochCalc.Poisson.CompensatedMartingaleAdapted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_SourceProof_8931f323c09204a87f59d757

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_ccdcfef1e11a997eb9caf4a9
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral N φ t)
      ℱ P := by
  refine ⟨LevyStochCalc.Poisson.Compensated.simpleIntegral_stronglyAdapted_compensated N ℱ hℱ φ h_adapt, ?_⟩
  intro s t hst
  have h_unfold_pi : ∀ u : ℝ, (fun ω => LevyStochCalc.Poisson.Compensated.simpleIntegral N φ u ω) =
      ∑ i : Fin φ.N, (fun ω : Ω => φ.ξ i ω * N.compensated (φ.timeRect i u) ω) := by
    intro u; ext ω; rw [Finset.sum_apply]; rfl
  change P[fun ω => LevyStochCalc.Poisson.Compensated.simpleIntegral N φ t ω | ℱ.seq s] =ᵐ[P]
    fun ω => LevyStochCalc.Poisson.Compensated.simpleIntegral N φ s ω
  rw [h_unfold_pi t, h_unfold_pi s]
  have h_int : ∀ i ∈ (Finset.univ : Finset (Fin φ.N)),
      MeasureTheory.Integrable
        (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P :=
    fun i _ => LevyStochCalc.Poisson.Compensated.simpleIntegral_term_integrable_compensated N φ i t
  refine (MeasureTheory.condExp_finsetSum h_int (m := ℱ.seq s)).trans ?_
  refine eventuallyEq_sum ?_
  intro i _
  exact _root_.Prove2MeSourceProof.h_8931f323c09204a87f59d757 N ℱ hℱ φ i (h_adapt i) hst
end LevyStochCalc.Poisson.Compensated


