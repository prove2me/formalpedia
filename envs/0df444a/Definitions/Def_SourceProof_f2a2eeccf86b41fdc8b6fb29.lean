-- Prove2me | Definitions.Def_SourceProof_f2a2eeccf86b41fdc8b6fb29
-- name    : SourceProof_f2a2eeccf86b41fdc8b6fb29
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:39:29.845178+00:00
-- url     : https://prove2.me/theorems/c4efa002-53c4-4066-8258-015b37abdd4e
-- title:
--   LevyStochCalc source module: SourceProof_f2a2eeccf86b41fdc8b6fb29
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.compensator_stronglyMeasurable` comes from the `LevyStochCalc.Poisson.CompensatedQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation martingale of the compensated integral

For an adapted mark-step integrand `G`, the compensated square
`t ↦ (∫_0^t ∫_E G dÑ)² − ∫_0^t ∫_E G(u, e)² ν(de) du` is a martingale on the natural
filtration: the increment isometries of `MarkStep` give the set-level identity required by
`LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral`. The compensated square of the
`L²` integral process is then the `L¹`-limit of the stage compensated squares.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)


theorem _root_.Prove2MeSourceProof.h_f2a2eeccf86b41fdc8b6fb29 (hG : G.Adapted ℱ) (t : ℝ) :
    @StronglyMeasurable Ω ℝ _ (ℱ t) (G.compensator t) := by
  rcases lt_or_ge t 0 with ht | ht
  · have h : (LevyStochCalc.Poisson.Compensated.MarkStep.compensator G) t = fun _ => 0 := funext fun ω => G.compensator_of_nonpos ht.le ω
    rw [h]
    exact stronglyMeasurable_const
  · let G' : @LevyStochCalc.Poisson.Compensated.MarkStep Ω (ℱ t) E _ ν _ (g.clamp t ht) :=
      @LevyStochCalc.Poisson.Compensated.MarkStep.mk Ω (ℱ t) E _ ν _ (g.clamp t ht) G.K G.B
        G.B_measurable G.B_finite
        (fun i k ω => if i < (g.clamp t ht).N₀ then G.ξ i k ω else 0)
        (fun i k => by
          obtain ⟨M, hM⟩ := G.ξ_bounded i k
          refine ⟨|M|, fun ω => ?_⟩
          split_ifs
          · exact (hM ω).trans (le_abs_self M)
          · rw [abs_zero]
            exact abs_nonneg M)
        (fun i k => by
          by_cases hi : i < (g.clamp t ht).N₀
          · simp only [hi, if_true]
            exact ((hG i (g.lt_of_lt_clampIndex hi).1 k).mono
              (ℱ.mono (g.lt_of_lt_clampIndex hi).2.le)).measurable
          · simp only [hi, if_false]
            exact measurable_const)
    have hev : ∀ u e ω, @LevyStochCalc.Poisson.Compensated.MarkStep.eval Ω (ℱ t) E _ ν _ (g.clamp t ht) G' u e ω
        = (LevyStochCalc.Poisson.Compensated.MarkStep.eval (G.clamp t ht)) u e ω := by
      intro u e ω
      unfold LevyStochCalc.Poisson.Compensated.MarkStep.eval
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      change _ * ∑ k : Fin G.K, (if i < (g.clamp t ht).N₀ then G.ξ i k ω else 0)
          * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = _ * ∑ k : Fin G.K, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
      simp only [hi, if_true]
    have hcomp : (LevyStochCalc.Poisson.Compensated.MarkStep.compensator G) t
        = @LevyStochCalc.Poisson.Compensated.MarkStep.compensator Ω (ℱ t) E _ ν _ (g.clamp t ht) G' t := by
      funext ω
      unfold LevyStochCalc.Poisson.Compensated.MarkStep.compensator
      refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
      beta_reduce
      rw [hev, (_root_.Prove2MeSourceProof.h_24d7e98c77e2168bb8fc8995 G) t ht, if_pos hu.2]
    rw [hcomp]
    exact (@LevyStochCalc.Poisson.Compensated.MarkStep.measurable_compensator Ω (ℱ t) E _ ν _ (g.clamp t ht) G'
      t).stronglyMeasurable
end MarkStep

end LevyStochCalc.Poisson.Compensated


