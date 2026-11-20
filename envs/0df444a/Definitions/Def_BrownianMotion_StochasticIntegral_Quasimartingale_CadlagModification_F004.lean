-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F004
-- name    : BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:10:47.989789+00:00
-- url     : https://prove2.me/theorems/ad578bba-9c78-44c7-bc1c-86d80eb4ad70
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_LeftLimWithin_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Predictable_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F003
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/

/-! # Cadlag modification of quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section CountableEvents

variable [OrderBot ι] {T : Set ι} {t : ι}

end CountableEvents

section RegularitySet

variable [OrderBot ι]

variable [TopologicalSpace ι] [OrderTopology ι]

end RegularitySet

variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

end Accumulation

open Function

/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModif X` with the following properties:
* `rightContModif X` is right-continuous
* `rightContModif X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModif X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModif X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModif X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

/-! ## Càdlàg modification of a quasimartingale

For a real quasimartingale `X` we define a process `cadlagModif X` with the following properties:
* `cadlagModif X` is càdlàg
* for all `t` outside a countable set, `cadlagModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `cadlagModif X` is a modification of `X`.
* if the filtration is right-continuous and complete, then `cadlagModif X` is adapted.

TODO: if `t ↦ μ[X t]` is right-continuous (in particular if `X` is a martingale),
then `cadlagModif X` is a modification of `X` without the assumption that `X`
is right-continuous in probability.

-/

lemma _root_.MeasureTheory.Martingale.integral_eq [SigmaFiniteFiltration μ 𝓕]
    (hX : Martingale X 𝓕 μ) (i j : ι) : ∫ ω, X i ω ∂μ = ∫ ω, X j ω ∂μ := by
  wlog hij : i ≤ j
  · exact (this hX j i (by grind)).symm
  conv_rhs => rw [← integral_condExp (𝓕.le i)]
  refine integral_congr_ae ?_
  filter_upwards [hX.2 i j hij] with _ heq using heq.symm
end ProbabilityTheory


