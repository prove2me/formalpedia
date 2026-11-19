-- Prove2me | Definitions.Def_SourceProof_2a8aafc9167b053f609af742
-- name    : SourceProof_2a8aafc9167b053f609af742
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:55:12.146643+00:00
-- url     : https://prove2.me/theorems/75b98dc6-1068-45e8-8b3b-e7614c303774
-- title:
--   LevyStochCalc source proof: ProbabilityTheory.ElementaryPredictableSet.integrable_integral_real
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_SimpleProcess_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/

/-! # Simple processes and elementary stochastic integral

## Main definitions

- `ElementaryPredictableSet`: the type of elementary predictable sets
- `SimpleProcess`: the type of simple processes, as a Module over ℝ
- `SimpleProcess.toFun`: simple process interpreted as a stochastic process, with a CoeFun instance
- `SimpleProcess.integral`: elementary stochastic integral
- `SimpleProcess.isPredictable`: simple processes are predictable

## Implementation notes

`SimpleProcess` consists of a value function as a `Finsupp`: `value : ι × ι →₀ Ω → E` and a
value at ⊥: `valueBot : Ω → E`. This allows the definition of operations like addition to be
defined naturally.

However, this makes the function `SimpleProcess.toFun` non-injective, so `SimpleProcess` is not
`FunLike`. In other words, two distinct elements `X Y : SimpleProcess E 𝓕` may produce the same
function `(⇑X : ι → Ω → E) = (⇑Y : ι → Ω → E)`.

There are subtleties that are caused by this: for example, by a nonnegative simple
process, we mean `X : SimpleProcess E 𝓕` with `0 ≤ X.valueBot` and `0 ≤ X.value`, which is not the
same as `0 ≤ (⇑X : ι → Ω → E)`.

Similarly, `ElementaryPredictableSet` is a data type that has a coercion to `Set (ι × Ω)`, but
this coercion is not injective, so it is not `SetLike`. This makes it easy to define the indicator
function of an elementary predictable set as a simple process by mapping respective datas
(which is why it also requires disjoint unions).

## TODO

- Generalize instance variables.
-/

@[expose] public section

open MeasureTheory Finset Filter ContinuousLinearMap
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [mE : MeasurableSpace E]
-- Note: separable space is needed for `ContinuousAdd.measurableMul₂` (which has the wrong name)
variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓕 : Filtration ι mΩ}

attribute [local measurability]
  measurableSet_predictable_singleton_bot_prod
  measurableSet_predictable_Ioi_prod
  measurableSet_predictable_Ioc_prod

namespace ElementaryPredictableSet

                                                                

end ElementaryPredictableSet

namespace SimpleProcess

                                        

-- todo: replace the condition on W by IsPredictable

section Module

-- TODO: Mathlib's Finset.measurable_prod is wrong because it is currently an exact duplicate of
-- Finset.measurable_fun_sum; we want the following version instead.

end Module

section ToFun

end ToFun

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section Integral

              
                                                      

              
                                                   

              
                                                                                

variable {B : E →L[ℝ] F →L[ℝ] G}

-- @[simp] lemma integral_top (V : SimpleProcess E 𝓕) (X : ι → Ω → F) (ω : Ω) :
--     integral B V X ⊤ ω = V.value.sum fun p v ↦ B (v ω) (X p.2 ω - X p.1 ω) := by simp [integral]

end Integral

section Assoc

section Bilin

section map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

-- Analogous to LinearMap.finsupp_sum_apply and AddMonoidHom.finsuppSum_apply:

end map₂

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {I : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I]
variable {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
variable [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]

end Bilin

section Comp

variable [SecondCountableTopology (F →L[ℝ] G)]
variable [SecondCountableTopology (E →L[ℝ] F)]
variable [SecondCountableTopology (E →L[ℝ] G)]
omit mE [SecondCountableTopology E]

end Comp

section SMul

-- TODO: cor:elemStochIntegral_assoc_real_bilin and lem:elemStochIntegral_assoc

end SMul

end Assoc

end SimpleProcess

section Indicator

namespace ElementaryPredictableSet

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open scoped SimpleProcess

theorem _root_.Prove2MeSourceProof.h_2a8aafc9167b053f609af742 {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hXint : ∀ s, Integrable (X s) μ) (S : ElementaryPredictableSet 𝓕) (c : ℝ) (t : ι) :
    Integrable (((S.indicator c) ● X) t) μ := by
  refine integrable_finsetSum _ fun p hp ↦ Integrable.bdd_mul
    (((hXint _).sub (hXint _))) ?_ (c := ‖c‖) (ae_of_all _ fun ω ↦ ?_)
  · simp only [ProbabilityTheory.ElementaryPredictableSet.value_indicator]
    split_ifs with hp
    swap; · fun_prop
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.indicator (by fun_prop) ?_
    have hmeas : MeasurableSet[𝓕 p.1] (S.set p) := S.measurableSet_set p hp
    exact 𝓕.le _ _ hmeas
  · simp only [ProbabilityTheory.ElementaryPredictableSet.value_indicator, Real.norm_eq_abs]
    split_ifs with hp
    · by_cases hω : ω ∈ S.set p <;> simp [hω]
    · simp
end ElementaryPredictableSet

end Indicator

section Predictable

namespace ElementaryPredictableSet

end ElementaryPredictableSet

namespace SimpleProcess

end SimpleProcess

end Predictable

end ProbabilityTheory


