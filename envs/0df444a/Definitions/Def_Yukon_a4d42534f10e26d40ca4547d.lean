-- Prove2me | Definitions.Def_Yukon_a4d42534f10e26d40ca4547d
-- name    : Yukon_a4d42534f10e26d40ca4547d
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:06:19.000237+00:00
-- url     : https://prove2.me/theorems/32e6da52-b846-4a61-bfa0-3e9ca050710a
-- title:
--   YukonModule.VCVio.EvalDist.Defs.AlternativeMonad.part0
-- statement:
--   Source module VCVio.EvalDist.Defs.AlternativeMonad.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Defs/AlternativeMonad.lean
--
--   yukon-proof-operation:592b5cbdbe0609ff5c0a92fea9f968c0bd1518ae7091e79ed6dc737f6d7f8b9a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NTkyYjVjYmRiZTA2MDlmZjVjMGE5MmZlYTlmOTY4YzBiZDE1MThhZTcwOTFlNzllZDZkYzczN2Y2ZDdmOGI5YSIsImhhc2giOiJhN2UyMWU4MGZmODVlYzVjNTNmZDRlNTU5ZDM1OWU2NzZkNjhkODVlNmE2ZDQzOTczNjVmNzBmZDVmNjdlNTU0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9hNGQ0MjUzNGYxMGUyNmQ0MGNhNDU0N2QiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
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
# Denotational Semantics Over `AlternativeMonad`.

This file defines `HasEvalSet.LawfulFailure`, a type-class refining `MonadLiftT m SetM` when
given an `AlternativeMonad` instance on the base monad, enforcing that `failure` maps to the
empty sub-distribution. Compatibility conditions then force the correct semantics for `evalDist`,
recorded in the `*_failure` simp lemmas below.
-/

@[expose] public section

open ENNReal HasEvalSet

universe u v w

variable {m : Type u → Type v} [AlternativeMonad m] {α β γ : Type u}

/-- Refinement of `MonadLiftT m SetM` when given an `AlternativeMonad` instance on the
base monad, enforcing that `failure` maps to the empty sub-distribution. Compatibility
conditions then force the correct semantics for `evalDist`, see below. -/
protected class HasEvalSet.LawfulFailure (m : Type u → Type v)
    [AlternativeMonad m] [MonadLiftT m SetM] : Prop where
  support_failure' {α : Type u} : support (failure : m α) = ∅

open HasEvalSet (LawfulFailure)

@[simp, grind =]
lemma support_failure [MonadLiftT m SetM] [LawfulFailure m] :
    support (failure : m α) = ∅ :=
  HasEvalSet.LawfulFailure.support_failure'

@[simp, grind =]
lemma finSupport_failure [MonadLiftT m SetM] [LawfulFailure m] [HasEvalFinset m]
    [DecidableEq α] : finSupport (failure : m α) = ∅ := by grind

@[simp, grind =]
lemma probOutput_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] (x : α) : Pr[= x | (failure : m α)] = 0 := by simp

@[simp, grind =]
lemma probEvent_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] (p : α → Prop) : Pr[ p | (failure : m α)] = 0 := by simp

@[simp, grind =]
lemma probFailure_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] :
    Pr[⊥ | (failure : m α)] = 1 := by simp

@[simp, grind =]
lemma evalDist_failure [MonadLiftT m SPMF] [MonadLiftT m SetM] [EvalDistCompatible m]
    [LawfulFailure m] : 𝒟[(failure : m α)] = SPMF.mk (PMF.pure none) := by simp


