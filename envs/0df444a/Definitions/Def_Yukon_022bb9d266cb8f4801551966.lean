-- Prove2me | Definitions.Def_Yukon_022bb9d266cb8f4801551966
-- name    : Yukon_022bb9d266cb8f4801551966
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:47:20.067451+00:00
-- url     : https://prove2.me/theorems/6cfe5b38-e978-44e7-9294-8a16d1aada4c
-- title:
--   YukonModule.ToMathlib.Control.OptionT.part0
-- statement:
--   Source module ToMathlib.Control.OptionT.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/ToMathlib/Control/OptionT.lean
--
--   yukon-proof-operation:8b771a8a53ae1d0d323255ffa5dda3cc75767ea561c09273af2b94c9c3563b39
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OGI3NzFhOGE1M2FlMWQwZDMyMzI1NWZmYTVkZGEzY2M3NTc2N2VhNTYxYzA5MjczYWYyYjk0YzljMzU2M2IzOSIsImhhc2giOiIxNjZkOGYyODlkZjIzMzlkZDVkMTIzMmQ0MzJhNGQ2NmMwM2FiYzI0MjIzMTAzMzBiZjIxNTgwMzZjNDdlZmFkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wMjJiYjlkMjY2Y2I4ZjQ4MDE1NTE5NjYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

-- import PolyFun.Control.Monad.Free
public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
public import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b

public import Definitions.Def_Yukon_ec6e56db18cc5472c07c58c9



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b
meta import Definitions.Def_Yukon_ec6e56db18cc5472c07c58c9
set_option backward.isDefEq.respectTransparency.types false
/-!
# Lemmas about `OptionT`
-/

@[expose] public section

universe u v w

namespace OptionT

variable {m : Type u → Type v} {n : Type u → Type w}
  (f : {α : Type u} → m α → n α) {α β γ : Type u}

lemma monad_pure_eq_pure [Monad m] (x : α) :
    (pure x : OptionT m α) = OptionT.pure x := rfl

lemma monad_bind_eq_bind [Monad m] (x : OptionT m α) (y : α → OptionT m β) :
    x >>= y = OptionT.bind x y := rfl

@[grind =]
lemma liftM_def {m : Type u → Type v} [Monad m] {α : Type u}
    (x : m α) : (x : OptionT m α) = OptionT.lift x := rfl

section mapM

/-- Canonical lifting of a map from `m α → n α` to one from `OptionT m α → n α`
given an `Alternative n` instance to handle failure. -/
protected def mapM {m : Type u → Type v} {n : Type u → Type w}
    [AlternativeMonad n] (f : {α : Type u} → m α → n α)
    {α : Type u} (x : OptionT m α) : n α :=
  do (← f x.run).getM

-- instance {m : Type u → Type v} {n : Type u → Type w}
--     [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
--     (f : {α : Type u} → m α → n α)
--     [MonadHomClass m n @f] :
--     MonadHomClass (OptionT m) n (@OptionT.mapM m n _ f) where
--   map_pure {α} x := by simp [OptionT.mapM]
--   map_bind {α β} mx my := by
--     simp [OptionT.mapM, Function.comp_def, Option.elimM]
--     refine congr_arg (f mx.run >>= ·) (funext fun x => ?_)
--     cases x <;> simp

/-- Bundled version of `mapM`.
dtumad: we should probably just pick one of these (probably the hom class non-bundled approach). -/
protected def mapM' {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) : OptionT m →ᵐ n where
  toFun _ x := do match (← f x.run) with
    | some x => return x
    | none => failure
  toFun_pure' x := by
    simp
  toFun_bind' x y := by
    simp only [run_bind, Option.elimM, MonadHom.toFun_bind', monad_norm]
    congr 1
    ext x; cases x; all_goals simp

@[simp]
lemma mapM'_lift {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) (x : m α) : OptionT.mapM' f (OptionT.lift x) = f x := by
  simp [OptionT.mapM', OptionT.lift]

@[simp]
lemma mapM'_failure {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [AlternativeMonad n] [LawfulMonad n] [LawfulAlternative n]
    (f : m →ᵐ n) : OptionT.mapM' f (failure : OptionT m α) = failure := by
  simp [OptionT.mapM']

end mapM

@[simp]
lemma mk_bind {α β} (m : Type u → Type v) [Monad m] [LawfulMonad m]
    (mx : m α) (my : α → m (Option β)) :
    OptionT.mk (mx >>= my) = liftM mx >>= fun x => OptionT.mk (my x) := by
  simp [OptionT.ext_iff]

@[simp, grind =]
lemma liftM_elimM {m} [Monad m] {α β}
    (x : m (Option α)) (y : m β) (z : α → m β)
    {n} [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
    (liftM (Option.elimM x y z) : n β) =
      Option.elimM (liftM x : n (Option α)) (liftM y) (fun x => liftM (z x)) := by
  simp only [Option.elimM, liftM_bind]
  refine bind_congr fun x => by cases x <;> simp

/-- Rewrite a mapped `OptionT.mk`'d bind through a pointwise `Option.map` relation between two
bodies: if `Option.map f <$> body₁ a` agrees with `Option.map (post a) <$> body₂ a` for every
sample `a`, then mapping `f` over `OptionT.mk (sample >>= body₁)` equals `OptionT.mk` of binding
`body₂` and post-processing with `post`. Useful for re-expressing a mapped `OptionT` computation
through an alternative body with sample-dependent post-processing. -/
lemma map_mk_bind_eq_of_body {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β γ δ : Type u}
    (sample : m α) (body₁ : α → m (Option β)) (body₂ : α → m (Option γ))
    (f : β → δ) (post : α → γ → δ)
    (hBody : ∀ a, Option.map f <$> body₁ a = Option.map (post a) <$> body₂ a) :
    f <$> OptionT.mk (do
      let a ← sample
      body₁ a)
    =
    OptionT.mk (do
      let a ← sample
      let r ← body₂ a
      pure (Option.map (post a) r)) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  simp only [OptionT.run_mk, map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext a
  rw [← map_eq_bind_pure_comp, hBody a, map_eq_bind_pure_comp]
  rfl

end OptionT


