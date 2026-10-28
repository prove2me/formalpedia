-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_StochasticIntegral_SimpleProcess
-- name    : KLSModular_BrownianMotion_StochasticIntegral_SimpleProcess
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:48:09.017887+00:00
-- url     : https://prove2.me/theorems/caf3671e-3746-4673-9446-528d081d9a4f
-- title:
--   Elementary predictable sets, simple processes, and elementary stochastic integrals
-- statement:
--   For a continuous bilinear map $B : E \toL[\mathbb R] F \toL[\mathbb R] G$, `SimpleProcess.integral` defines the elementary stochastic integral $V\,\!\mathbin{\bullet_B}\,X$ by summing $B$ applied to the process value and the stopped-process increment between the endpoints of each interval; `integralEval` and the scoped notations `●L` and `●` provide evaluation and scalar special cases. The indicator process `ElementaryPredictableSet.indicator` takes the value $e$ on the corresponding measurable pieces and $0$ elsewhere, and `integral_indicator_apply` gives its finite-sum integral formula. The auxiliary result `integrable_integral_real` states that this integral is integrable for a real-valued process whose value at every time is integrable.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.StoppedProcess
--   public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
--   public import Mathlib.Order.CompletePartialOrder
--   public import Mathlib.Probability.Process.Predictable
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure ElementaryPredictableSet (𝓕 : Filtration ι mΩ) where
--     /-- The set over `⊥`. -/
--     setBot : Set Ω
--     /-- The finite index for sets over `(s, t]`. -/
--     I : Finset (ι × ι)
--     /-- The sets over `(s, t]`. -/
--     set : ι × ι → Set Ω
--     le_of_mem_I : ∀ p ∈ I, p.1 ≤ p.2
--     measurableSet_setBot : MeasurableSet[𝓕 ⊥] setBot
--     measurableSet_set : ∀ p ∈ I, MeasurableSet[𝓕 p.1] (set p)
--     pairwiseDisjoint : Set.PairwiseDisjoint ↑I (fun p : ι × ι ↦ Set.Ioc p.1 p.2 ×ˢ set p)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/StoppedProcess`](https://prove2.me/theorems/b4c3b2bd-27ef-4c9e-ad42-8ef7fe087414).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/StochasticIntegral/SimpleProcess.lean) · `BrownianMotion.StochasticIntegral.SimpleProcess` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/StochasticIntegral/SimpleProcess.lean#L67-L783 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.StochasticIntegral.SimpleProcess`, definition bundle `KLSModular_BrownianMotion_StochasticIntegral_SimpleProcess`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_StoppedProcess
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Process.Predictable

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/StochasticIntegral/SimpleProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory Finset Filter ContinuousLinearMap
open scoped ENNReal Topology
noncomputable section
namespace ProbabilityTheory
variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
variable [NormedAddCommGroup E] [mE : MeasurableSpace E]
variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓕 : Filtration ι mΩ}
attribute [local measurability]
  measurableSet_predictable_singleton_bot_prod
  measurableSet_predictable_Ioi_prod
  measurableSet_predictable_Ioc_prod
/-- An **elementary predictable set** is a finite disjoint union of sets of the form `{⊥} × B` for
`B ∈ 𝓕 ⊥` and of the form `(s, t] × B` for `s < t` in `ι` and `B ∈ 𝓕 s`.

Note that we require the union to be disjoint. This is not necessary, but makes it easier to define
the indicator function of an elementary predictable set as a `SimpleProcess`. -/
structure ElementaryPredictableSet (𝓕 : Filtration ι mΩ) where
  /-- The set over `⊥`. -/
  setBot : Set Ω
  /-- The finite index for sets over `(s, t]`. -/
  I : Finset (ι × ι)
  /-- The sets over `(s, t]`. -/
  set : ι × ι → Set Ω
  le_of_mem_I : ∀ p ∈ I, p.1 ≤ p.2
  measurableSet_setBot : MeasurableSet[𝓕 ⊥] setBot
  measurableSet_set : ∀ p ∈ I, MeasurableSet[𝓕 p.1] (set p)
  pairwiseDisjoint : Set.PairwiseDisjoint ↑I (fun p : ι × ι ↦ Set.Ioc p.1 p.2 ×ˢ set p)
namespace ElementaryPredictableSet
attribute [measurability] measurableSet_setBot measurableSet_set
/-- Coercion from an `ElementaryPredictableSet 𝓕` to a `Set (ι × Ω)`. -/
@[coe] def toSet (S : ElementaryPredictableSet 𝓕) : Set (ι × Ω) :=
    {⊥} ×ˢ S.setBot ∪ ⋃ p ∈ S.I, (Set.Ioc p.1 p.2) ×ˢ S.set p
instance : CoeOut (ElementaryPredictableSet 𝓕) (Set (ι × Ω)) where
  coe := toSet
end ElementaryPredictableSet
/-- A **simple process** is defined as a finite sum of indicator functions of intervals `(s, t]`,
each assigned to a bounded `𝓕 s`-measurable random variable `value`, plus a `valueBot` at ⊥. -/
@[ext]
structure SimpleProcess (F : Type*) [NormedAddCommGroup F] [MeasurableSpace F] [NormedSpace ℝ F]
    [BorelSpace F] [SecondCountableTopology F] (𝓕 : Filtration ι mΩ) where
  /-- The value at ⊥. -/
  valueBot : Ω → F
  /-- The value on each interval. Note that intervals are not necessarily disjoint. -/
  value : ι × ι →₀ Ω → F
  /-- The intervals in the support of `value` are ordered. -/
  le_of_mem_support_value : ∀ p ∈ value.support, p.1 ≤ p.2
  /-- The value at ⊥ is measurable with respect to the filtration at ⊥. -/
  measurable_valueBot : Measurable[𝓕 ⊥] valueBot := by
    first | measurability | eta_expand; measurability
  /-- The value on each interval is measurable with respect to the filtration at the left endpoint.

  Do not use this lemma directly. Use `SimpleProcess.measurable_value` instead. -/
  measurable_value' : ∀ p ∈ value.support, Measurable[𝓕 p.1] (value p) := by
    -- Note: Most of the time we need to eta-expand to make `fun_prop` find the right lemma,
    -- such as `Measurability.neg` that can only recognize `fun x ↦ -f x` rather than `-f`.
    -- On the other hand, some other lemmas like `Measurable.const_smul` can only recognize `c • f`
    -- rather than `fun x ↦ c • f x`, so we also need to try directly applying `measurability`.
    first | measurability | eta_expand; measurability
  /-- The value at ⊥ is bounded. -/
  bounded_valueBot : ∃ C : ℝ, ∀ ω : Ω, ‖valueBot ω‖ ≤ C
  /-- The value on each interval is bounded. -/
  bounded_value : ∃ C : ℝ, ∀ p ∈ value.support, ∀ ω : Ω, ‖value p ω‖ ≤ C
namespace SimpleProcess
attribute [fun_prop] measurable_valueBot
/-- A bound on the value at ⊥. -/
noncomputable def valueBotBound (V : SimpleProcess E 𝓕) : ℝ := max 0 V.bounded_valueBot.choose
/-- The value at ⊥ is bounded by `valueBotBound`. -/
@[simp] lemma valueBot_le_valueBotBound (V : SimpleProcess E 𝓕) (ω : Ω) :
    ‖V.valueBot ω‖ ≤ V.valueBotBound :=
  le_max_of_le_right (V.bounded_valueBot.choose_spec ω)
/-- The value of the simple process at the left endpoint of an interval is measurable
with respect to the filtration at the left endpoint.

Note that we do not require `p ∈ V.value.support`, because the value is 0 otherwise,
which is measurable. -/
@[fun_prop]
lemma measurable_value (V : SimpleProcess E 𝓕) (p : ι × ι) : Measurable[𝓕 p.1] (V.value p) := by
  by_cases hp : p ∈ V.value.support
  · exact V.measurable_value' p hp
  · rw [show V.value p = 0 by simpa using hp]
    exact measurable_const
/-- A nonnegative bound on the value on each interval. -/
noncomputable def valueBound (V : SimpleProcess E 𝓕) : ℝ := max 0 (V.bounded_value.choose)
/-- The value on each interval is bounded by `valueBound`. Note that we do not require
`p ∈ V.value.support`. -/
@[simp] lemma value_le_valueBound (V : SimpleProcess E 𝓕) (p : ι × ι) (ω : Ω) :
    ‖V.value p ω‖ ≤ V.valueBound := by
  by_cases hp : p ∈ V.value.support
  · exact le_max_of_le_right (V.bounded_value.choose_spec p hp ω)
  · apply le_max_of_le_left
    rw [show V.value p = 0 by simpa using hp]
    simp
section Module
@[simps]
instance instZero : Zero (SimpleProcess E 𝓕) where
  zero := {
    valueBot := 0,
    value := 0,
    le_of_mem_support_value := by simp,
    bounded_valueBot := ⟨0, by simp⟩,
    bounded_value := ⟨0, by simp⟩ }
@[simps]
instance instNeg : Neg (SimpleProcess E 𝓕) where
  neg V := {
    valueBot := -V.valueBot,
    value := -V.value,
    le_of_mem_support_value := by simpa using V.le_of_mem_support_value,
    bounded_valueBot := ⟨V.valueBotBound, by simp⟩,
    bounded_value := ⟨V.valueBound, by simp⟩ }
@[simps]
instance instAdd : Add (SimpleProcess E 𝓕) where
  add V W := {
    valueBot := V.valueBot + W.valueBot,
    value := V.value + W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_add hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    measurable_value' p hp := by
      simp only [Finsupp.coe_add, Pi.add_apply]
      exact Measurable.add (by fun_prop) (by fun_prop)
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_add_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_add_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }
@[simps]
instance instSub : Sub (SimpleProcess E 𝓕) where
  sub V W := {
    valueBot := V.valueBot - W.valueBot,
    value := V.value - W.value,
    le_of_mem_support_value := fun p hp ↦ (mem_union.1 (Finsupp.support_sub hp)).elim
      (V.le_of_mem_support_value p) (W.le_of_mem_support_value p),
    measurable_value' p hp := by
      simp only [Finsupp.coe_sub, Pi.sub_apply]
      exact Measurable.sub (by fun_prop) (by fun_prop)
    bounded_valueBot := ⟨V.valueBotBound + W.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_sub_le, V.valueBot_le_valueBotBound, W.valueBot_le_valueBotBound]⟩,
    bounded_value := ⟨V.valueBound + W.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_sub_le, V.value_le_valueBound, W.value_le_valueBound]⟩ }
@[simps]
instance instSMul : SMul ℝ (SimpleProcess E 𝓕) where
  smul c V := {
    valueBot := c • V.valueBot,
    value := c • V.value,
    le_of_mem_support_value := by simpa using fun p _ ↦ V.le_of_mem_support_value p,
    bounded_valueBot := ⟨|c| * V.valueBotBound, fun ω ↦ by
      dsimp
      grw [norm_smul, V.valueBot_le_valueBotBound, Real.norm_eq_abs]⟩,
    bounded_value := ⟨|c| * V.valueBound, fun p _ ω ↦ by
      dsimp
      grw [norm_smul, V.value_le_valueBound, Real.norm_eq_abs]⟩ }
instance instAddCommGroup : AddCommGroup (SimpleProcess E 𝓕) where
  sub_eq_add_neg U V := by ext <;> apply sub_eq_add_neg
  add_assoc U V W := by ext <;> apply add_assoc
  add_comm U V := by ext <;> apply add_comm
  zero_add V := by ext <;> apply zero_add
  add_zero V := by ext <;> apply add_zero
  neg_add_cancel V := by ext <;> apply neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec
instance instModule : Module ℝ (SimpleProcess E 𝓕) where
  zero_smul V := by ext <;> simp
  smul_zero V := by ext <;> simp
  add_smul U V W := by ext <;> simp [add_smul]
  smul_add U V W := by ext <;> simp [smul_add]
  one_smul V := by ext <;> simp
  mul_smul U V W := by ext <;> simp [mul_smul]
end Module
section ToFun
/-- Coercion from a simple process to a function. Note that this is not injective. -/
@[coe] def toFun (V : SimpleProcess E 𝓕) (i : ι) (ω : Ω) : E :=
  ({⊥} : Set ι).indicator (fun _ ↦ V.valueBot ω) i
    + V.value.sum fun p v => (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) i
instance instCoeFun : CoeFun (SimpleProcess E 𝓕) (fun _ ↦ ι → Ω → E) where
  coe := toFun
end ToFun
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
section Integral
/-- The **elementary stochastic integral** with respect to a continuous bilinear map `B`. -/
def integral (B : E →L[ℝ] F →L[ℝ] G) (V : SimpleProcess E 𝓕) (X : ι → Ω → F) :
    ι → Ω → G :=
  fun i ω ↦ V.value.sum fun p v =>
    B (v ω) (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)
@[inherit_doc]
scoped notation:25 V " ●[" B "]" X => integral B V X
/-- The **linear elementary stochastic integral** where the simple process takes values in
`E →L[ℝ] F`, as a special case of `integral` with `B` the evaluation map. -/
abbrev integralEval [SecondCountableTopology (E →L[ℝ] F)] (V : SimpleProcess (E →L[ℝ] F) 𝓕)
    (X : ι → Ω → E) : ι → Ω → F :=
  V ●[(.id ℝ (E →L[ℝ] F))] X
@[inherit_doc]
scoped notation:25 V " ●L " X => integralEval V X
@[inherit_doc]
scoped notation:25 V " ● " X => integral (ContinuousLinearMap.mul ℝ ℝ) V X
variable {B : E →L[ℝ] F →L[ℝ] G}
end Integral
end SimpleProcess
section Indicator
namespace ElementaryPredictableSet
/-- The indicator function of an elementary predictable set as a simple process.
This takes value `0` at time not in `S`, and `e` at time `S`. -/
def indicator (S : ElementaryPredictableSet 𝓕) (e : E) : SimpleProcess E 𝓕 where
  valueBot := S.setBot.indicator fun _ ↦ e
  value := Finsupp.onFinset S.I (fun p ↦ if p ∈ S.I then (S.set p).indicator fun _ ↦ e else 0)
    (by simp +contextual)
  le_of_mem_support_value := fun p hp ↦ S.le_of_mem_I p (Finsupp.support_onFinset_subset hp)
  bounded_valueBot := ⟨‖e‖, fun _ ↦ norm_indicator_le_norm_self _ _⟩
  bounded_value := ⟨‖e‖, fun _ _ _ ↦ by
    rw [Finsupp.onFinset_apply]
    split_ifs
    · exact norm_indicator_le_norm_self _ _
    · simp⟩
  measurable_value' := fun p hp ↦ by
    rw [Finsupp.onFinset_apply]
    measurability
@[simp]
lemma value_indicator (S : ElementaryPredictableSet 𝓕) (c : E) (p : ι × ι) :
    (S.indicator c).value p = if p ∈ S.I then (S.set p).indicator fun _ ↦ c else 0 := by
  unfold ElementaryPredictableSet.indicator SimpleProcess.value
  simp only [Finsupp.onFinset_apply]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- Explicit formula for `1_S ● X` where `S` is an elementary predictable set. -/
lemma integral_indicator_apply (S : ElementaryPredictableSet 𝓕)
    (e : E) (B : E →L[ℝ] F →L[ℝ] G) (X : ι → Ω → F) (i : ι) (ω : Ω) :
    (S.indicator e).integral B X i ω = ∑ p ∈ S.I, (S.set p).indicator (fun ω ↦
      B e (stoppedProcess X (fun _ ↦ i) p.2 ω - stoppedProcess X (fun _ ↦ i) p.1 ω)) ω := by
  rw [SimpleProcess.integral, indicator, Finsupp.onFinset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos hp, Set.indicator, Set.indicator]
    split_ifs <;> simp
  simp
open scoped SimpleProcess
lemma integrable_integral_real {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hXint : ∀ s, Integrable (X s) μ) (S : ElementaryPredictableSet 𝓕) (c : ℝ) (t : ι) :
    Integrable (((S.indicator c) ● X) t) μ := by
  refine integrable_finsetSum _ fun p hp ↦ Integrable.bdd_mul
    (((hXint _).sub (hXint _))) ?_ (c := ‖c‖) (ae_of_all _ fun ω ↦ ?_)
  · simp only [ElementaryPredictableSet.value_indicator]
    split_ifs with hp
    swap; · fun_prop
    refine StronglyMeasurable.aestronglyMeasurable ?_
    refine StronglyMeasurable.indicator (by fun_prop) ?_
    have hmeas : MeasurableSet[𝓕 p.1] (S.set p) := S.measurableSet_set p hp
    exact 𝓕.le _ _ hmeas
  · simp only [ElementaryPredictableSet.value_indicator, Real.norm_eq_abs]
    split_ifs with hp
    · by_cases hω : ω ∈ S.set p <;> simp [hω]
    · simp
end ElementaryPredictableSet
end Indicator
end ProbabilityTheory


