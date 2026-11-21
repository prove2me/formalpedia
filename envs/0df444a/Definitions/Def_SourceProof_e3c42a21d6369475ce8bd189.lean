-- Prove2me | Definitions.Def_SourceProof_e3c42a21d6369475ce8bd189
-- name    : SourceProof_e3c42a21d6369475ce8bd189
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:52:37.001721+00:00
-- url     : https://prove2.me/theorems/6b9ef916-e857-4f2f-814a-3ba33485ef7a
-- title:
--   LevyStochCalc source module: SourceProof_e3c42a21d6369475ce8bd189
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi` comes from the `LevyStochCalc.Ito.JumpSplittingLeftLim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Finite-activity splitting along the left limits of the path

The jump coefficient of a jump diffusion can be evaluated along the left limits of the path
instead of along the path itself. The two integrands agree off a countable set of times, so they
have the same compensated integral, while the pathwise integral against the random measure and
the compensator against the reference intensity are both taken with the left-limit integrand.
The drift carrying the compensator of the left-limit integrand agrees with the drift carrying
that of the path integrand at almost every time of every horizon, so the two build the same
vector Itô process.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPath` — the left limits of the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeft` — the pathwise sum of the jumps carried by a mark
  set over a time window, with the jump coefficient evaluated at the left limits of the path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeft` — the drift of a jump diffusion with the
  compensator of the left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSumLeft_nhdsWithin_Ioi` — the left-limit jump sum
  over `(0, ·]` is right-continuous in time.
* `LevyStochCalc.Ito.JumpSplitting.ae_ae_restrict_continuousDriftLeft_eq` and
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_vectorItoProcess_continuousDriftLeft_eq` — the two
  drifts agree at almost every time of every horizon, hence build the same vector Itô process.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section WindowContinuity

variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_e3c42a21d6369475ce8bd189 {κ : Measure (ℝ × E)} {A : Set E}
    (hA : MeasurableSet A) {f : ℝ × E → ℝ} (hf : Measurable f)
    (hint : ∀ T : ℝ, IntegrableOn f (Set.Ioc (0 : ℝ) T ×ˢ A) κ) (t : ℝ) :
    Tendsto (fun s => ∫ q in Set.Ioc (0 : ℝ) s ×ˢ A, f q ∂κ) (𝓝[>] t)
      (𝓝 (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, f q ∂κ)) := by
  have hrw : ∀ s : ℝ, (∫ q in Set.Ioc (0 : ℝ) s ×ˢ A, f q ∂κ)
      = ∫ q, (Set.Ioc (0 : ℝ) s ×ˢ A).indicator f q ∂κ :=
    fun s => (integral_indicator (measurableSet_Ioc.prod hA)).symm
  simp only [hrw]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    ((Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator fun q : ℝ × E => ‖f q‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun s =>
      (hf.indicator (measurableSet_Ioc.prod hA)).aestronglyMeasurable
  · filter_upwards [(ge_mem_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds] with s hs
    refine Filter.Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A
    · have hq' : q ∈ Set.Ioc (0 : ℝ) (t + 1) ×ˢ A := ⟨⟨hq.1.1, hq.1.2.trans hs⟩, hq.2⟩
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
    · have hnn : (0 : ℝ) ≤ (Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
          (fun q : ℝ × E => ‖f q‖) q :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) q
      rw [Set.indicator_of_notMem hq]
      simpa using hnn
  · exact (MeasureTheory.integrable_indicator_iff (measurableSet_Ioc.prod hA)).mpr
      (hint (t + 1)).norm
  · refine Filter.Eventually.of_forall fun q => ?_
    have key : ∀ᶠ s in 𝓝[>] t,
        (Set.Ioc (0 : ℝ) t ×ˢ A).indicator f q = (Set.Ioc (0 : ℝ) s ×ˢ A).indicator f q := by
      by_cases hqA : q.2 ∈ A
      · by_cases hq0 : 0 < q.1
        · by_cases hqt : q.1 ≤ t
          · filter_upwards [eventually_mem_nhdsWithin] with s hs
            have h1 : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A := ⟨⟨hq0, hqt.trans (le_of_lt hs)⟩, hqA⟩
            have h2 : q ∈ Set.Ioc (0 : ℝ) t ×ˢ A := ⟨⟨hq0, hqt⟩, hqA⟩
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · have ht' : t < q.1 := not_le.mp hqt
            filter_upwards [(gt_mem_nhds ht').filter_mono nhdsWithin_le_nhds] with s hs
            have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr hs)
            have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr ht')
            rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        · refine Filter.Eventually.of_forall fun s => ?_
          have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hq0 hmem.1.1
          have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hq0 hmem.1.1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      · refine Filter.Eventually.of_forall fun s => ?_
        have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hqA hmem.2
        have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hqA hmem.2
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    exact Filter.Tendsto.congr' key tendsto_const_nhds
end WindowContinuity

end LevyStochCalc.Ito.JumpSplitting


