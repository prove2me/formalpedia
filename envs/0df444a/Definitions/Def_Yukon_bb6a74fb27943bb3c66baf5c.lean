-- Prove2me | Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c
-- name    : Yukon_bb6a74fb27943bb3c66baf5c
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:12:11.590986+00:00
-- url     : https://prove2.me/theorems/80b94c49-36ee-43f8-ae35-85aac38e416f
-- title:
--   YukonModule.VCVio.EvalDist.Monad.Map.part0
-- statement:
--   Source module VCVio.EvalDist.Monad.Map. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Monad/Map.lean
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Monad/Map.lean
--
--   yukon-proof-operation:f9c98ed169664434b476bcab78a1e643c3980be6e88ebe5c2569cf8da1c91f29
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjljOThlZDE2OTY2NDQzNGI0NzZiY2FiNzhhMWU2NDNjMzk4MGJlNmU4OGViZTVjMjU2OWNmOGRhMWM5MWYyOSIsImhhc2giOiIzZmM1Mzc3YTgxZGQ0ZGIwNWUyMGEyNTNlODc0MWY0OWQ4NDVhZjA0MmYyZjU3Nzg3MmY3YjAwYThjOGUwZmQxIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iYjZhNzRmYjI3OTQzYmIzYzY2YmFmNWMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_10be02bf5325c192ea9b6156



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Definitions.Def_Yukon_0169f95fdb4d5928b3998f5a
public import Definitions.Def_Yukon_c042061a45cc167df49b6d76
public import Definitions.Def_Yukon_ece90b6202ec9f124162dcb0
meta import Definitions.Def_Yukon_0169f95fdb4d5928b3998f5a
meta import Definitions.Def_Yukon_c042061a45cc167df49b6d76
meta import Definitions.Def_Yukon_ece90b6202ec9f124162dcb0
meta import Definitions.Def_Yukon_10be02bf5325c192ea9b6156
set_option backward.isDefEq.respectTransparency.types false
/-!
# Evaluation Distributions of Computations with `map`

File for lemmas about `evalDist` and `support` involving the monadic `map`.

Note: we focus on lemmas that don't hold naively when reducing `<$>` to `>>=` using monad laws,
since `map_eq_bind_pure_comp` can be applied to use `bind` lemmas fairly easily.
Instead we focus on the cases like `f <$> mx` for injective `f`, which allow stronger statements.
More generally we can consier `f` with `InjOn f (support mx)` and get good lemmas.

TODO: many lemmas should probably have mirrored `bind_pure` versions.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

@[simp, grind =]
lemma support_map [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [LawfulMonad m]
    (f : α → β) (mx : m α) :
    support (f <$> mx) = f '' support mx := by
  aesop (add simp monad_norm)

@[simp, grind =]
lemma finSupport_map [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [HasEvalFinset m] [LawfulMonad m]
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (mx : m α) : finSupport (f <$> mx) = (finSupport mx).image f := by
  grind [map_eq_bind_pure_comp]

@[simp, grind =]
lemma evalDist_map [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m]
    (mx : m α) (f : α → β) :
    𝒟[f <$> mx] = f <$> (𝒟[mx]) := by simp [monad_norm]

lemma evalDist_map_eq_of_evalDist_eq [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m]
    {mx my : m α} (h : 𝒟[mx] = 𝒟[my]) (f : α → β) :
    𝒟[f <$> mx] = 𝒟[f <$> my] := by
  simpa [evalDist_map] using congrArg (fun p => f <$> p) h

lemma probOutput_map_eq_of_evalDist_eq [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m]
    {mx my : m α} (h : 𝒟[mx] = 𝒟[my]) (f : α → β) (y : β) :
    Pr[= y | f <$> mx] = Pr[= y | f <$> my] :=
  evalDist_ext_iff.mp (evalDist_map_eq_of_evalDist_eq h f) y

@[simp]
lemma evalDist_comp_map [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [LawfulMonad m] (mx : m α) :
    evalDist ∘ (fun f => f <$> mx) = fun f : (α → β) => f <$> 𝒟[mx] := by aesop

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α) (f : α → β)

@[simp, grind =]
lemma probEvent_bind_pure_comp (q : β → Prop) :
    Pr[ q | mx >>= pure ∘ f] = Pr[ q ∘ f | mx] := by
  have := Classical.decPred q
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  simp only [Function.comp_apply, probEvent_pure, mul_ite, mul_one, mul_zero] <;> rfl

variable [LawfulMonad m]

/-- Write the probability of an output after mapping the result of a computation as a sum
over all outputs such that they map to the correct final output, using subtypes.
This lemma notably doesn't require decidable equality on the final type, unlike most
lemmas about probability when mapping a computation. -/
lemma probOutput_map_eq_tsum_subtype [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] (y : β) :
    Pr[= y | f <$> mx] = ∑' x : {x ∈ support mx | y = f x}, Pr[= x | mx] := by
  simp only [map_eq_bind_pure_comp, tsum_subtype _, probOutput_bind_eq_tsum, Function.comp_apply,
    Set.indicator, Set.mem_setOf_eq]
  refine tsum_congr fun x => ?_
  by_cases hy : y = f x <;> by_cases hx : x ∈ support mx <;>
    simp [hy, hx, probOutput_eq_zero_of_not_mem_support]

lemma probOutput_map_eq_tsum (y : β) :
    Pr[= y | f <$> mx] = ∑' x, Pr[= x | mx] * Pr[= y | (pure (f x) : m β)] := by
  simp [monad_norm, probOutput_bind_eq_tsum]

lemma probOutput_map_eq_tsum_subtype_ite [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑' x : support mx, if y = f x then Pr[= x | mx] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum_subtype, Function.comp_apply,
    probOutput_pure, mul_ite, mul_one, mul_zero]

@[grind =]
lemma probOutput_map_eq_tsum_ite [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑' x : α, if y = f x then Pr[= x | mx] else 0 := by
  simp only [map_eq_bind_pure_comp, probOutput_bind_eq_tsum, Function.comp_apply, probOutput_pure,
    mul_ite, mul_one, mul_zero]

@[grind =]
lemma probOutput_map_eq_sum_fintype_ite [Fintype α] [DecidableEq β] (y : β) :
    Pr[= y | f <$> mx] = ∑ x : α, if y = f x then Pr[= x | mx] else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans (tsum_eq_sum' <|
    by simp only [Finset.coe_univ, Set.subset_univ])

@[grind =]
lemma probOutput_map_eq_sum_finSupport_ite [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    (y : β) : Pr[= y | f <$> mx] = ∑ x ∈ finSupport mx, if y = f x then Pr[= x | mx] else 0 :=
  (probOutput_map_eq_tsum_ite mx f y).trans (tsum_eq_sum' <|
    by simp only [coe_finSupport, Function.support_subset_iff, ne_eq, ite_eq_right_iff,
      probOutput_eq_zero_iff', mem_finSupport_iff_mem_support, Classical.not_imp, not_not, and_imp,
      imp_self, implies_true])

@[grind =]
lemma probOutput_map_eq_sum_filter_finSupport [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [EvalDistCompatible m] [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    (y : β) : Pr[= y | f <$> mx] = ∑ x ∈ (finSupport mx).filter (y = f ·), Pr[= x | mx] := by
  rw [Finset.sum_filter, probOutput_map_eq_sum_finSupport_ite]

@[simp, grind =]
lemma probFailure_map : Pr[⊥ | f <$> mx] = Pr[⊥ | mx] := by
  simp [monad_norm, probFailure_bind_eq_add_tsum]

@[simp, grind =]
lemma probEvent_map (q : β → Prop) : Pr[ q | f <$> mx] = Pr[ q ∘ f | mx] := by
  grind [= map_eq_bind_pure_comp]

/-- Outcome probability of a `map`, as a pulled-back event: `Pr[= y | f <$> mx]` is the probability
that the source lands in the `f`-preimage of `y`. The `probOutput` companion to `probEvent_map`.
Tagged `@[grind =]` only (not `@[simp]`): `simp` keeps its injective/equiv-map normal forms
(`probOutput_map_equiv`, `…_eq_probOutput_inverse`), which this pulled-back-event form would clash
with. -/
@[grind =]
lemma probOutput_map (y : β) : Pr[= y | f <$> mx] = Pr[ fun x => f x = y | mx] := by
  rw [← probEvent_eq_eq_probOutput, probEvent_map]; rfl

lemma probEvent_comp (q : β → Prop) : Pr[ q ∘ f | mx] = Pr[ q | f <$> mx] :=
  symm <| probEvent_map mx f q

lemma probFailure_eq_sub_sum_probOutput_map [Fintype β] (mx : m α) (f : α → β) :
    Pr[⊥ | mx] = 1 - ∑ y : β, Pr[= y | f <$> mx] := by
  rw [← probFailure_map (f := f), probFailure_eq_sub_tsum, tsum_fintype]

@[aesop safe apply]
lemma probOutput_map_eq_single [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {f : α → β} {y : β}
    (x : α) (h : ∀ x' ∈ support mx, y = f x' → x = x') (h' : f x = y) :
    Pr[= y | f <$> mx] = Pr[= x | mx] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single x fun x' hx' => ?_).trans (by rw [h', probOutput_pure_self, mul_one])
  specialize h x'
  by_cases hx' : x' ∈ support mx
  · simp only [mul_eq_zero]
    aesop
  · simp [probOutput_eq_zero_of_not_mem_support hx']

section const

variable (mx : m α) (y : β)

omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[aesop safe norm, grind .]
lemma support_map_const [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (hx : (support mx).Nonempty) :
    support ((fun _ => y) <$> mx) = {y} := by
  aesop

omit [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] in
@[simp, grind .]
lemma finSupport_map_const [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [DecidableEq α] [DecidableEq β] [HasEvalFinset m]
    (hx : (finSupport mx).Nonempty) : finSupport ((fun _ => y) <$> mx) =
      if (finSupport mx).Nonempty then {y} else ∅ := by
  grind

@[simp, aesop safe norm, grind =_]
lemma probOutput_map_const [MonadLiftT m SetM] [EvalDistCompatible m] (y' : β) :
    Pr[= y' | (fun _ => y) <$> mx] =
      (1 - Pr[⊥ | mx]) * Pr[= y' | (pure y : m β)] := by
  simp only [monad_norm, Function.comp_def, probOutput_bind_const]

@[simp, aesop safe norm, grind =_]
lemma probEvent_map_const [MonadLiftT m SetM] [EvalDistCompatible m] (p : β → Prop) :
    Pr[ p | (fun _ => y) <$> mx] =
      (1 - Pr[⊥ | mx]) * Pr[ p | (pure y : m β)] := by
  simp only [monad_norm, Function.comp_def, probEvent_bind_const]

@[simp, aesop safe norm]
lemma probEvent_map_const' [MonadLiftT m SetM] [EvalDistCompatible m] (p : β → Prop)
    [DecidablePred p] :
    Pr[ p | (fun _ => y) <$> mx] =
      if p y then (1 - Pr[⊥ | mx]) else 0 := by
  simp [Function.comp_def]

end const

section inverse

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
  {f : α → β} {g : β → α} {y : β}

@[aesop safe norm]
lemma probOutput_map_eq_probOutput_of_leftInvOn
    (hr : Set.LeftInvOn g f (support mx)) (hy : f (g y) = y) :
    Pr[= y | f <$> mx] = Pr[= g y | mx] := by
  rw [probOutput_map_eq_tsum]
  refine (tsum_eq_single (g y) fun x hx => ?_).trans (by aesop)
  by_cases hx : x ∈ support mx
  · specialize hr hx
    aesop
  · aesop

lemma probOutput_map_eq_probOutput_inverse
    (hl : Function.LeftInverse g f) (hy : f (g y) = y) :
    Pr[= y | f <$> mx] = Pr[= g y | mx] := by aesop

lemma probOutput_map_eq_probOutput_apply
    (hl : f (g y) = y) (hr : ∀ y, g (f y) = y) :
    Pr[= y | f <$> mx] = Pr[= g y | mx] := by aesop

@[simp, grind =]
lemma probOutput_map_equiv (e : α ≃ β) (mx : m α) (y : β) :
    Pr[= y | e <$> mx] = Pr[= e.symm y | mx] := by aesop

end inverse

section injective

@[grind .]
lemma probOutput_map_injective (mx : m α) {f : α → β} (hf : f.Injective) (x : α) :
    Pr[= f x | f <$> mx] = Pr[= x | mx] := by
  classical
  rw [map_eq_bind_pure_comp, probOutput_bind_eq_tsum]
  refine (tsum_eq_single x fun y hy => ?_).trans (by
    simp only [Function.comp_apply, probOutput_pure_self, mul_one])
  simp only [Function.comp_apply, probOutput_pure, mul_ite, mul_one, mul_zero]
  exact if_neg fun h => hy (hf h.symm)

lemma probOutput_map_eq_probOutput (mx : m α)
    {f : α → β} (hf : ∀ x x', f x = f x' → x = x') (x : α) :
    Pr[= f x | f <$> mx] = Pr[= x | mx] :=
  probOutput_map_injective mx hf x

section support

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

@[aesop safe norm]
lemma probOutput_map_eq_probOutput_invFunOn [Nonempty α]
    (mx : m α) {f : α → β} (hf : Set.InjOn f (support mx))
    (y : β) (hy : ∃ x ∈ support mx, f x = y) :
    Pr[= y | f <$> mx] = Pr[= Function.invFunOn f (support mx) y | mx] := by
  rw [probOutput_map_eq_probOutput_of_leftInvOn]
  · intro x hx
    have h : ∃ y ∈ support mx, f y = f x := ⟨x, hx, rfl⟩
    specialize hf (Classical.choose_spec h).1 hx (Classical.choose_spec h).2
    rw [Function.invFunOn]
    aesop
  rw [Function.invFunOn, dif_pos hy, (Classical.choose_spec hy).2]

end support

end injective


