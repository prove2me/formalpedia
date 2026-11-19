-- Prove2me | Definitions.Def_BrownianMotion_StochasticIntegral_SimpleProcess_F001
-- name    : BrownianMotion_StochasticIntegral_SimpleProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:41:06.212266+00:00
-- url     : https://prove2.me/theorems/46bfdb64-72eb-4b94-bb94-d9970db3f2de
-- title:
--   Source declarations: BrownianMotion.StochasticIntegral.SimpleProcess
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.StochasticIntegral.SimpleProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

end ElementaryPredictableSet

end Indicator

section Predictable

namespace ElementaryPredictableSet

@[measurability]
theorem measurableSet_predictable (S : ElementaryPredictableSet 𝓕) :
    MeasurableSet[𝓕.predictable] ↑S := by
  apply MeasurableSet.union
  · measurability
  · apply MeasurableSet.biUnion (Finset.countable_toSet _)
    measurability
variable (ι Ω) in
/-- The elementary predictable sets generate the predictable σ-algebra. Note that we require the
time domain to have countably generated `atTop` so that each `(t, ∞]` can be written as a countable
union of intervals `(t, s]`. -/
theorem generateFrom_eq_predictable [(Filter.atTop : Filter ι).IsCountablyGenerated] :
    MeasurableSpace.generateFrom {↑S | S : ElementaryPredictableSet 𝓕} = 𝓕.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨S, rfl⟩
    exact S.measurableSet_predictable
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro B₀ hB₀
      apply MeasurableSpace.measurableSet_generateFrom
      use singletonBotProd hB₀, coe_singletonBotProd hB₀
    · intro t B hB
      obtain ⟨seq, _, tendsto⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
      have : Set.Ioi t = ⋃ n : ℕ, Set.Ioc t (seq n) := by
        ext s
        suffices ∃ n, s ≤ seq n by simpa using fun _ ↦ this
        rw [Filter.tendsto_atTop_atTop] at tendsto
        obtain ⟨n, h⟩ := tendsto s
        exact ⟨n, h n le_rfl⟩
      rw [this, Set.iUnion_prod_const]
      refine MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom ?_
      use IocProd t (seq n) hB, coe_IocProd _ _ hB
end ElementaryPredictableSet

namespace SimpleProcess

theorem isStronglyPredictable (V : SimpleProcess E 𝓕) : IsStronglyPredictable 𝓕 V := by
  apply Measurable.stronglyMeasurable
  apply Measurable.add
  · apply Measurable.indicator
    · intro s hs
      suffices MeasurableSet[𝓕.predictable] (({⊥} ∪ Set.Ioi ⊥) ×ˢ (V.valueBot ⁻¹' s)) by
        convert this
        ext; simp
      rw [Set.union_prod]
      measurability
    · change MeasurableSet[𝓕.predictable] {a | a.1 = ⊥}
      suffices MeasurableSet[𝓕.predictable] ({⊥} ×ˢ Set.univ) by
        convert this
        ext; simp
      measurability
  · apply measurable_sum
    intro p hp s hs
    suffices MeasurableSet[𝓕.predictable]
        ((Set.Ioc p.1 p.2)ᶜ ×ˢ ((fun _ ↦ 0) ⁻¹' s) ∪ Set.Ioc p.1 p.2 ×ˢ (V.value p ⁻¹' s)) by
      convert this
      ext ⟨i, ω⟩
      simp only [Set.indicator, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_compl_iff]
      split_ifs with h <;> simp [h]
    apply MeasurableSet.union
    · have : (Set.Ioc p.1 p.2)ᶜ = {⊥} ∪ Set.Ioc ⊥ p.1 ∪ Set.Ioi p.2 := by
        rw [Set.compl_Ioc, ← Set.Icc_bot, ← Set.Ioc_union_left bot_le, Set.union_comm {⊥}]
      rw [this, Set.union_prod, Set.union_prod]
      measurability
    · measurability
variable (E 𝓕) in
theorem iSup_comap_eq_predictable [(Filter.atTop : Filter ι).IsCountablyGenerated]
    [MeasurableSingletonClass E] [Nontrivial E] :
    (⨆ V : SimpleProcess E 𝓕, mE.comap (Function.uncurry ⇑V)) = 𝓕.predictable := by
  apply le_antisymm
  · rw [iSup_le_iff]
    intro V
    simp [(isStronglyPredictable V).measurable.comap_le]
  · rw [← ElementaryPredictableSet.generateFrom_eq_predictable]
    apply MeasurableSpace.generateFrom_le
    rintro _ ⟨S, rfl⟩
    simp_rw [MeasurableSpace.measurableSet_iSup, MeasurableSpace.measurableSet_comap]
    apply MeasurableSpace.GenerateMeasurable.basic
    let ⟨(e : E), f_ne⟩ := exists_ne 0
    use S.indicator e, {e}, measurableSet_singleton e
    simp only [ElementaryPredictableSet.coe_indicator, ElementaryPredictableSet.toSet,
      Function.uncurry_curry]
    classical
    erw [Set.indicator_const_preimage_eq_union]
    simp [f_ne.symm]
end SimpleProcess

end Predictable

end ProbabilityTheory


