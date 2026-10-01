-- Prove2me | Definitions.Def_Yukon_bea5afc7edc0c83512a59496
-- name    : Yukon_bea5afc7edc0c83512a59496
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:56.306507+00:00
-- url     : https://prove2.me/theorems/c17c9576-e981-467c-b274-048a5d10b9b4
-- title:
--   YukonModule.VCVio.EvalDist.Instances.ReaderT.part0
-- statement:
--   Source module VCVio.EvalDist.Instances.ReaderT.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Instances/ReaderT.lean
--
--   yukon-proof-operation:c5c3d55670b96593bd861a2bf2494e9768c1a7166a9fe88fa06d2f1a95f4681b
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YzVjM2Q1NTY3MGI5NjU5M2JkODYxYTJiZjI0OTRlOTc2OGMxYTcxNjZhOWZlODhmYTA2ZDJmMWE5NWY0NjgxYiIsImhhc2giOiJiYTgwMDJlZTJiMTI4ZGY4ZjY0NTNhOTgxNzViNzBhZTczNjdlZjc1ZThlNzFhYzk0YjMzMzkwZjBmM2Q4Y2VjIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iZWE1YWZjN2VkYzBjODM1MTJhNTk0OTYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_c042061a45cc167df49b6d76



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_c042061a45cc167df49b6d76
set_option backward.isDefEq.respectTransparency.types false
/-!
# Evaluation Semantics for ReaderT

This file provides monad homomorphisms for evaluating `ReaderT ρ m` computations
by fixing the environment parameter.

Unlike `StateT`, `ReaderT` evaluation at a fixed environment is a valid monad homomorphism
because the environment is read-only and doesn't change during computation.

## Main definitions

* `ReaderT.evalAt ρ0`: Monad homomorphism `ReaderT ρ m →ᵐ m` by evaluation at `ρ0`
* `ReaderT.toSPMF ρ0`: Lift `MonadLiftT m SPMF` through `ReaderT` at fixed `ρ0`
* `ReaderT.toPMF ρ0`: Lift `MonadLiftT m PMF` through `ReaderT` at fixed `ρ0`

## Design notes

We do NOT provide global `MonadLiftT (ReaderT ρ m) SPMF` instances because there's no
canonical choice of environment. Instead, users explicitly provide the environment
when constructing the evaluation homomorphism.

For cryptographic games with random oracles, the typical pattern is:
1. Generate oracle table with some distribution
2. Use `toSPMF`/`toPMF` to evaluate the protocol at that table
3. Compose with the table distribution to get overall game probability

-/

@[expose] public section

universe u v

variable {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

namespace ReaderT

/-- Evaluate a `ReaderT` computation at a fixed environment `ρ0`.
This is a monad homomorphism because `ReaderT` is read-only. -/
def evalAt (ρ0 : ρ) : ReaderT ρ m →ᵐ m where
  toFun {α} (mx : ReaderT ρ m α) := mx ρ0
  toFun_pure' _ := rfl
  toFun_bind' _ _ := rfl

@[simp] lemma evalAt_apply (ρ0 : ρ) (mx : ReaderT ρ m α) :
    evalAt ρ0 mx = mx ρ0 := rfl

@[simp] lemma evalAt_pure (ρ0 : ρ) (x : α) :
    evalAt (m := m) ρ0 (pure x : ReaderT ρ m α) = pure x := rfl

@[simp] lemma evalAt_bind (ρ0 : ρ) (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    evalAt ρ0 (mx >>= f) = evalAt ρ0 mx >>= fun x => evalAt ρ0 (f x) := rfl

/-- Lift `m → SPMF` to a homomorphism `ReaderT ρ m →ᵐ SPMF` by fixing `ρ0`.

This allows evaluating reader computations to sub-probability distributions
when the base monad `m` has such an evaluation. -/
noncomputable def toSPMF (ρ0 : ρ) [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    ReaderT ρ m →ᵐ SPMF :=
  MonadHom.ofLift m SPMF ∘ₘ evalAt ρ0

/-- Lift `m → PMF` to a homomorphism `ReaderT ρ m →ᵐ PMF` by fixing `ρ0`. -/
noncomputable def toPMF (ρ0 : ρ) [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] :
    ReaderT ρ m →ᵐ PMF :=
  MonadHom.ofLift m PMF ∘ₘ evalAt ρ0

section evalDist_lemmas

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (ρ0 : ρ)

/-- Evaluating `pure x` at any environment gives the same result as `pure x` in the base monad. -/
@[simp] lemma toSPMF_pure (x : α) :
    toSPMF ρ0 (pure x : ReaderT ρ m α) = (liftM (pure x : m α) : SPMF α) := rfl

/-- Evaluating a bind distributes through the monad homomorphism. -/
@[simp] lemma toSPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    toSPMF ρ0 (mx >>= f) = toSPMF ρ0 mx >>= fun x => toSPMF ρ0 (f x) :=
  (toSPMF ρ0).toFun_bind' mx f

end evalDist_lemmas

section evalPMF_lemmas

variable [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] (ρ0 : ρ)

@[simp] lemma toPMF_pure (x : α) :
    toPMF ρ0 (pure x : ReaderT ρ m α) = (liftM (pure x : m α) : PMF α) := rfl

@[simp] lemma toPMF_bind (mx : ReaderT ρ m α) (f : α → ReaderT ρ m β) :
    toPMF ρ0 (mx >>= f) = toPMF ρ0 mx >>= fun x => toPMF ρ0 (f x) :=
  (toPMF ρ0).toFun_bind' mx f

end evalPMF_lemmas

end ReaderT


