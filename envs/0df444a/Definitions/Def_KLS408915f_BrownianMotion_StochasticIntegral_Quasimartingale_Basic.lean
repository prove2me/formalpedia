-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
-- name    : KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:39:57.826748+00:00
-- url     : https://prove2.me/theorems/cc247901-044d-40d3-b448-00b0187df0d3
-- title:
--   Real quasimartingales and variation bounds
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `IsRealQuasimartingale 𝓕 X μ` requires that the real process $X$ is adapted, integrable at every time, and has a uniform upper bound on the expectations of all elementary predictable indicator integrals. `variationBound X 𝓕 μ t` is the supremum of those integral expectations over elementary predictable sets. The bundle proves that each such expectation is bounded by `variationBound` and that a real quasimartingale is strongly adapted.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/Quasimartingale/Basic.lean#L28-L50 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.Quasimartingale.Basic`, definition bundle `KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_SimpleProcess
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/StochasticIntegral/Quasimartingale/Basic.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped Function ProbabilityTheory.SimpleProcess
namespace ProbabilityTheory
variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ}
/-- A real quasimartingale is a real-valued stochastic process that is adapted, integrable,
and has bounded variation. -/
structure IsRealQuasimartingale (𝓕 : Filtration ι mΩ) (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  adapted : Adapted 𝓕 X
  integrable : ∀ t, Integrable (X t) μ
  boundedVariation :
    ∀ t, ∃ C, ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C
/-- The minimal bound on the variation of the process. -/
noncomputable
def variationBound (X : ι → Ω → ℝ) (𝓕 : Filtration ι mΩ) (μ : Measure Ω) (t : ι) : ℝ :=
  ⨆ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t]
lemma IsRealQuasimartingale.integral_indicator_le_variationBound (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (S : ElementaryPredictableSet 𝓕) :
    μ[(S.indicator (1 : ℝ) ● X) t] ≤ variationBound X 𝓕 μ t := by
  unfold variationBound
  refine le_ciSup (f := fun S ↦ ∫ x, (S.indicator 1 ● X) t x ∂μ) ?_ S
  obtain ⟨C, hC⟩ := hX.boundedVariation t
  exact ⟨C, by simp [mem_upperBounds, hC]⟩
lemma IsRealQuasimartingale.stronglyAdapted (hX : IsRealQuasimartingale 𝓕 X μ) :
    StronglyAdapted 𝓕 X := hX.adapted.stronglyAdapted
end ProbabilityTheory


