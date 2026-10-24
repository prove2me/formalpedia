-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
-- name    : KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:37:35.523133+00:00
-- url     : https://prove2.me/theorems/831ba693-d63d-4bbe-a8f8-17efb7a4bc6a
-- title:
--   Within-set one-sided limits and regularization
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `Function.leftLimWithin` defines a left limit along a set in a linearly ordered domain, using the function value when the within-left filter is trivial or no limit exists; `rightLimWithin` is the dual definition. The bundle proves basic filter identities, identifies these definitions at isolated points, and proves convergence to the defined limit whenever a limit exists. For dense sets, `continuousWithinAt_leftLimWithin_Iic_of_dense` and its right-sided analogue establish continuity of the regularized function on the full one-sided closed interval under the stated limit and isolated-point hypotheses.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/LeftLimWithin.lean#L24-L312 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.LeftLimWithin`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Separation.Regular

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/LeftLimWithin.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open Set Filter
open Topology
lemma nhdsWithin_inf_principal {E : Type*} [TopologicalSpace E] (s t : Set E) (x : E) :
    𝓝[s] x ⊓ 𝓟 t = 𝓝[s ∩ t] x := by
  rw [nhdsWithin, nhdsWithin, inf_assoc, inf_principal, Set.inter_comm]
section
variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]
/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the left of `f` at `a`, denoted with `leftLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its left or the function has no left
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.leftLimWithin (f : α → β) (s : Set α) (a : α) : β := by
  classical
  haveI : Nonempty β := ⟨f a⟩
  letI : TopologicalSpace α := Preorder.topology α
  exact if 𝓝[Set.Iio a ∩ s] a = ⊥ ∨ ¬∃ y, Tendsto f (𝓝[Set.Iio a ∩ s] a) (𝓝 y) then f a else
    limUnder (𝓝[Set.Iio a ∩ s] a) f
/-- Let `f : α → β` be a function from a linear order `α` to a topological space `β`, and
let `a : α`. The limit strictly to the right of `f` at `a`, denoted with `rightLim f a`, is defined
by using the order topology on `α`. If `a` is isolated to its right or the function has no right
limit, we use `f a` instead to guarantee a good behavior in most cases. -/
noncomputable def Function.rightLimWithin (f : α → β) (s : Set α) (a : α) : β :=
  @Function.leftLimWithin αᵒᵈ β _ _ f s a
open Function
/-- If `s` is dense and `𝓝[<] a` is not bot, then `a` is a left-accumulation point of `s`. -/
lemma nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[<] a).NeBot] :
    (𝓝[Iio a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Iio a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Iio) hne
  exact ⟨x, hx.1, hx.2, hxs⟩
/-- If `s` is dense and `𝓝[>] a` is not bot, then `a` is a right-accumulation point of `s`. -/
lemma nhdsWithin_Ioi_inter_neBot_of_nhdsGT_neBot [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : Dense s) (a : α) [(𝓝[>] a).NeBot] :
    (𝓝[Ioi a ∩ s] a).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
  intro U hU haU
  have hne : (U ∩ Ioi a).Nonempty :=
    mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 inferInstance) U hU haU
  obtain ⟨x, hxs, hx⟩ := hs.exists_mem_open (hU.inter isOpen_Ioi) hne
  exact ⟨x, hx.1, hx.2, hxs⟩
lemma leftLimWithin_eq_of_eq_bot [hα : TopologicalSpace α] [h'α : OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Iio a ∩ s] a = ⊥) : leftLimWithin f s a = f a := by
  rw [h'α.topology_eq_generate_intervals] at h
  simp [leftLimWithin, h]
lemma rightLimWithin_eq_of_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β)
    {s : Set α} {a : α} (h : 𝓝[Ioi a ∩ s] a = ⊥) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_eq_bot (α := αᵒᵈ) f h
/-- At a point which is isolated on the left, the within left limit is the value of the
function. -/
lemma leftLimWithin_eq_of_nhdsLT_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β)
    (s : Set α) {a : α} (h : 𝓝[<] a = ⊥) : leftLimWithin f s a = f a :=
  leftLimWithin_eq_of_eq_bot f (eq_bot_mono (nhdsWithin_mono _ inter_subset_left) h)
/-- At a point which is isolated on the right, the within right limit is the value of the
function. -/
lemma rightLimWithin_eq_of_nhdsGT_eq_bot [TopologicalSpace α] [OrderTopology α] (f : α → β)
    (s : Set α) {a : α} (h : 𝓝[>] a = ⊥) : rightLimWithin f s a = f a :=
  leftLimWithin_eq_of_nhdsLT_eq_bot (α := αᵒᵈ) f s h
lemma tendsto_leftLimWithin_of_tendsto [TopologicalSpace α] [h'α : OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)) := by
  rcases eq_or_neBot (𝓝[Iio a ∩ s] a) with h' | h'
  · simp [h']
  rw [h'α.topology_eq_generate_intervals] at h h' ⊢
  simp only [leftLimWithin, neBot_iff.1 h', h, not_true_eq_false, or_self, ↓reduceIte]
  exact tendsto_nhds_limUnder h
lemma tendsto_rightLimWithin_of_tendsto [TopologicalSpace α] [OrderTopology α]
    {f : α → β} {s : Set α} {a : α} (h : ∃ y, Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 y)) :
    Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)) :=
  tendsto_leftLimWithin_of_tendsto (α := αᵒᵈ) h
/-- Dense version of `continuousWithinAt_leftLimWithin_Iic` with the stronger conclusion that the
regularisation is continuous along the *full* left neighbourhood `Iic a`. This needs `s` dense (so
that the within-neighbourhood is `NeBot` at the points which are not isolated on the left), the
single-point hypothesis `h` that `f` has a within left limit at `a`, and that `f` has a within
left limit at every point eventually to the left of `a`.

At a point `c` which is isolated on the left, `leftLimWithin f s c = f c`, hence we need those
points to belong to `s` (hypothesis `hs'`). If the order is densely ordered, there are no such
points to the left of `a`, except possibly a minimal element. -/
lemma continuousWithinAt_leftLimWithin_Iic_of_dense [TopologicalSpace α] [OrderTopology α]
    [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (hs' : ∀ᶠ c in 𝓝[<] a, 𝓝[<] c = ⊥ → c ∈ s)
    (h : Tendsto f (𝓝[Iio a ∩ s] a) (𝓝 (leftLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[<] a, Tendsto f (𝓝[Iio c ∩ s] c) (𝓝 (leftLimWithin f s c))) :
    ContinuousWithinAt (leftLimWithin f s) (Iic a) a := by
  rw [← continuousWithinAt_Iio_iff_Iic]
  by_cases ha : ∃ b, b < a
  swap
  · have hempty : Set.Iio a = ∅ := Set.eq_empty_iff_forall_notMem.2 fun u hu ↦ ha ⟨u, hu⟩
    simp [ContinuousWithinAt, hempty]
  apply (closed_nhds_basis (Function.leftLimWithin f s a)).tendsto_right_iff.2
  rintro V ⟨V_mem, V_closed⟩
  have hev : ∀ᶠ x in 𝓝[<] a ⊓ 𝓟 s, f x ∈ V := by
    rw [nhdsWithin_inf_principal]; exact h.eventually V_mem
  obtain ⟨u, hua, hu⟩ := (nhdsLT_basis_of_exists_lt ha).eventually_iff.1
    (Filter.eventually_inf_principal.1 hev)
  filter_upwards [Ioo_mem_nhdsLT hua, hlim, hs'] with c hc hlimc hcs
  -- if `c` is isolated on the left, then `leftLimWithin f s c = f c` and `c ∈ s`
  rcases eq_or_neBot (𝓝[<] c) with h'c | h'c
  · have h''c : 𝓝[Iio c ∩ s] c = ⊥ := eq_bot_mono (nhdsWithin_mono _ inter_subset_left) h'c
    simpa [leftLimWithin_eq_of_eq_bot _ h''c] using hu hc (hcs h'c)
  have hne := nhdsWithin_Iio_inter_neBot_of_nhdsLT_neBot hs c
  refine V_closed.mem_of_tendsto hlimc ?_
  rw [← nhdsWithin_inf_principal]
  refine Filter.eventually_inf_principal.2 ?_
  filter_upwards [Ioo_mem_nhdsLT hc.1] with x hx hxs
  grind
/-- Dense version of `continuousWithinAt_rightLimWithin_Ici` with
the stronger conclusion `Ici a`. The points which are isolated on the right need to belong
to `s`, see `continuousWithinAt_leftLimWithin_Iic_of_dense`. -/
lemma continuousWithinAt_rightLimWithin_Ici_of_dense [TopologicalSpace α] [OrderTopology α]
    [T3Space β] {f : α → β} {s : Set α} {a : α} (hs : Dense s)
    (hs' : ∀ᶠ c in 𝓝[>] a, 𝓝[>] c = ⊥ → c ∈ s)
    (h : Tendsto f (𝓝[Ioi a ∩ s] a) (𝓝 (rightLimWithin f s a)))
    (hlim : ∀ᶠ c in 𝓝[>] a, Tendsto f (𝓝[Ioi c ∩ s] c) (𝓝 (rightLimWithin f s c))) :
    ContinuousWithinAt (rightLimWithin f s) (Ici a) a :=
  continuousWithinAt_leftLimWithin_Iic_of_dense (α := αᵒᵈ) hs hs' h hlim
end
open Function


