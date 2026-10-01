-- Prove2me | Definitions.Def_Yukon_253c1feebadee49aac5da140
-- name    : Yukon_253c1feebadee49aac5da140
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:27:16.571138+00:00
-- url     : https://prove2.me/theorems/f18fbb7a-7c2d-4407-a70b-d793d8836ed8
-- title:
--   YukonModule.VCVio.EvalDist.Defs.NeverFails.part0
-- statement:
--   Source module VCVio.EvalDist.Defs.NeverFails.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Defs/NeverFails.lean
--
--   yukon-proof-operation:49206bdd58e1a34af56fa2b2ce0732c3490a742c45374e86d0c8a81796d5a649
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NDkyMDZiZGQ1OGUxYTM0YWY1NmZhMmIyY2UwNzMyYzM0OTBhNzQyYzQ1Mzc0ZTg2ZDBjOGE4MTc5NmQ1YTY0OSIsImhhc2giOiIwMjhkYzAzNmMwMDM4MmE2ZTNhZTEwYjQ0MzE4YWM1YjkzNzIwOWM3N2NhYWQxYTM3NDkxNWUwMTAyYWQxOTcwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8yNTNjMWZlZWJhZGVlNDlhYWM1ZGExNDAiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import Definitions.Def_Yukon_a4d42534f10e26d40ca4547d

public import Definitions.Def_Yukon_641302f1e500c2a544b42adc



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_a4d42534f10e26d40ca4547d
meta import Definitions.Def_Yukon_641302f1e500c2a544b42adc
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computations that Never Fail

This file defines a predicate-as-typeclass stating that a probabilistic computation never
produces failure mass, together with lemmas for how the property behaves under common
monadic combinators.

Given a `MonadLiftT m SPMF` instance and a computation `mx : m α` in that monad,
`NeverFail mx` means
that `Pr[⊥ | mx] = 0`, i.e. that the computation never fails.

Defined as a typeclass to allow it to be synthesized automatically in certain cases.
However we don't include any instances for `bind` as this blows up the search space.
Instances involving `bind` should be added manually as needed.

The existence of a `MonadLiftT m PMF` instance implies that `NeverFail mx` holds for any computation
in the monad, since the `PMF` doesn't allow any probability of failing.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

/--
`NeverFail mx` states that the computation `mx : m α` has zero probability of failure,
equivalently the mass of `(evalDist mx)` at `none` is `0`.

Formally: `NeverFail mx` iff `Pr[⊥ | mx] = 0`.

Remarks:
- This class is a predicate (Prop-valued). It does not add data.
- Use the lemmas in this file (e.g. `bind_of_mem_support`) to transport the property through
  monadic structure. We intentionally avoid a `bind` instance, as the natural condition depends
  on the support of the left-hand side.
-/
class NeverFail {α : Type u} {m : Type u → Type v} [Monad m]
    [MonadLiftT m SPMF] (mx : m α) : Prop where
  mk :: probFailure_eq_zero : Pr[⊥ | mx] = 0

export NeverFail (probFailure_eq_zero)

attribute [simp] probFailure_eq_zero
attribute [aesop safe apply] NeverFail.mk

/-- Version of `probFailure_eq_zero` that avoids typeclass search. -/
lemma probFailure_eq_zero' [MonadLiftT m SPMF]
    {mx : m α} (h : NeverFail mx) : Pr[⊥ | mx] = 0 :=
  NeverFail.probFailure_eq_zero

/-- A computation in a monad with a total `PMF` lift can't fail. -/
instance  _root_.instNeverFailOfLawfulMonadLiftTPMF [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] (mx : m α) : NeverFail mx where
  probFailure_eq_zero := probFailure_of_liftM_PMF mx

section neverFail_lemmas

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

omit [LawfulMonadLiftT m SPMF] in
@[grind =]
lemma neverFail_iff (mx : m α) : NeverFail mx ↔ Pr[⊥ | mx] = 0 :=
  ⟨by aesop, NeverFail.mk⟩

@[simp, grind =]
lemma neverFail_bind_iff [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) (my : α → m β) :
    NeverFail (mx >>= my) ↔ NeverFail mx ∧ ∀ x ∈ support mx, NeverFail (my x) := by
  simp [neverFail_iff, probFailure_bind_eq_add_tsum_support, add_eq_zero]

@[simp, grind =]
lemma neverFail_map_iff [LawfulMonad m] (mx : m α) (f : α → β) :
    NeverFail (f <$> mx) ↔ NeverFail mx := by
  grind [= map_eq_bind_pure_comp]

@[simp]
lemma neverFail_seq_iff [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (mf : m (α → β)) (mx : m α) :
    NeverFail (mf <*> mx) ↔ NeverFail mf ∧ NeverFail mx := by
  simp only [seq_eq_bind_map, neverFail_bind_iff, neverFail_map_iff]
  refine ⟨fun ⟨hf, h⟩ => ⟨hf, ?_⟩, fun ⟨hf, hx⟩ => ⟨hf, fun _ _ => hx⟩⟩
  have hne : (support mf).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  exact h _ hne.choose_spec

@[simp]
lemma not_neverFail_failure {m : Type u → Type v} [AlternativeMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalSet.LawfulFailure m] :
    ¬ NeverFail (failure : m α) := by
  simp [neverFail_iff]

end neverFail_lemmas

namespace NeverFail

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

omit [LawfulMonadLiftT m SPMF] in
lemma of_probFailure_eq_zero (mx : m α) (h : Pr[⊥ | mx] = 0) : NeverFail mx :=
  { probFailure_eq_zero := h }

/--
If `mx` is a pure return, it never fails.
This follows since `evalDist pure x` is the Dirac distribution on `some x`.
-/
@[simp, grind .]
instance instPure {x} : NeverFail (pure x : m α) where
  probFailure_eq_zero := by simp [probFailure]

/--
Precise bind lemma: if `mx` never fails and for all `x` in the support of `mx` the continuation
`my x` never fails, then the whole bind never fails.

Sketch: using `evalDist_bind` and the identity

  `Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑ x, Pr[= x | mx] * Pr[⊥ | my x]`,

the first term vanishes by `NeverFail mx`, while for `x ∉ support mx` the coefficient
`Pr[= x | mx]` is `0`, and for `x ∈ support mx` the second factor vanishes by hypothesis.
Hence the sum is `0`.
-/
lemma bind_of_mem_support [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : α → m β}
    [hx : NeverFail mx] (hy : ∀ x ∈ support mx, NeverFail (my x)) :
    NeverFail (mx >>= my) where
  probFailure_eq_zero := ((neverFail_bind_iff mx my).mpr ⟨hx, hy⟩).probFailure_eq_zero

/--
Weak bind lemma: if the right-hand side never fails for every possible input (`∀ x`),
then the bind never fails.

This is a convenience corollary of `bind_of_mem_support`; it is often easy to apply when
`my` is uniform in its input (e.g. ignores it) or is known to be never-failing globally.
-/
lemma bind_of_forall [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : α → m β}
    [hx : NeverFail mx] [hy : ∀ x, NeverFail (my x)] :
    NeverFail (mx >>= my) := bind_of_mem_support (hx := hx) (fun x _ => hy x)

/--
Mapping a value through a total function preserves `NeverFail`.
-/
@[simp, grind .]
instance instMap [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} [h : NeverFail mx] (f : α → β) :
    NeverFail (f <$> mx) := by
  simp only [monad_norm, bind_of_forall, Function.comp_def]

/-- If both the function computation and the argument computation never fail,
then their applicative sequencing also never fails. -/
@[simp, grind .]
instance instSeq [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    {mf : m (α → β)} {mx : m α}
    [hf : NeverFail mf] [hx : NeverFail mx] :
    NeverFail (mf <*> mx) := by aesop

/-- If `mx` and `my` never fail, then `mx <* my` never fails. -/
@[simp, grind .]
instance instSeqLeft [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx <* my) := by aesop

/-- If `mx` and `my` never fail, then `mx *> my` never fails. -/
@[simp, grind .]
instance instSeqRight [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx *> my) := by aesop

example [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) [h : NeverFail mx] : NeverFail (do
    let x ← mx
    let y ← mx
    return (x, y)) := by
  grind

end NeverFail


