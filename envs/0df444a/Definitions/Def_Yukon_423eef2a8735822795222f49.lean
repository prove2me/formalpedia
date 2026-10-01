-- Prove2me | Definitions.Def_Yukon_423eef2a8735822795222f49
-- name    : Yukon_423eef2a8735822795222f49
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:38.462642+00:00
-- url     : https://prove2.me/theorems/667d6d75-9685-4d28-957b-2bec7aeecedf
-- title:
--   YukonModule.VCVio.EvalDist.Bool.part0
-- statement:
--   Source module VCVio.EvalDist.Bool.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Bool.lean
--
--   yukon-proof-operation:70b7b4637f5164f776bcc33b794d71cef2edfd823ee9581a99f0cd3ac8e90fb1
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NzBiN2I0NjM3ZjUxNjRmNzc2YmNjMzNiNzk0ZDcxY2VmMmVkZmQ4MjNlZTk1ODFhOTlmMGNkM2FjOGU5MGZiMSIsImhhc2giOiI3NDgxNjU4YTQ3NTdkZmQyOTVmNDZiMDgzODhlMzcyYmRkYmFlN2M2NTNiZGQ0ZWM5MDA0NDEwZjYxMjY2NWJhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl80MjNlZWYyYTg3MzU4MjI3OTUyMjJmNDkiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_253c1feebadee49aac5da140

public import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_253c1feebadee49aac5da140
meta import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c
set_option backward.isDefEq.respectTransparency.types false
/-!
# Evaluation Distributions on Boolean-Valued Computations

Specialization lemmas for `MonadLiftT m SPMF` computations returning `Bool`.
-/

@[expose] public section

variable {m : Type _ → Type _} [Monad m] [MonadLiftT m SPMF] {α β : Type _}

omit [Monad m] in
@[simp, grind =]
lemma probOutput_true_add_false (mx : m Bool) :
    Pr[= true | mx] + Pr[= false | mx] = 1 - Pr[⊥ | mx] := by
  simpa using tsum_probOutput_eq_sub mx

omit [Monad m] in
@[simp, grind =]
lemma probOutput_false_add_true (mx : m Bool) :
    Pr[= false | mx] + Pr[= true | mx] = 1 - Pr[⊥ | mx] := by
  rw [add_comm, probOutput_true_add_false]

omit [Monad m] in
lemma probOutput_true_eq_sub (mx : m Bool) :
    Pr[= true | mx] = 1 - Pr[⊥ | mx] - Pr[= false | mx] := by
  rw [← probOutput_true_add_false]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm

omit [Monad m] in
lemma probOutput_false_eq_sub (mx : m Bool) :
    Pr[= false | mx] = 1 - Pr[⊥ | mx] - Pr[= true | mx] := by
  rw [← probOutput_false_add_true]
  exact (ENNReal.add_sub_cancel_right probOutput_ne_top).symm

@[simp]
lemma probOutput_not_map [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    Pr[= true | (! ·) <$> mx] = Pr[= false | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) false

@[simp]
lemma probOutput_not_map' [LawfulMonad m] [LawfulMonadLiftT m SPMF] (mx : m Bool) :
    Pr[= false | (! ·) <$> mx] = Pr[= true | mx] :=
  probOutput_map_injective mx (fun a b h => by cases a <;> cases b <;> simp_all) true

@[grind =]
lemma probOutput_true_add_false_of_neverFail {mx : m Bool} [NeverFail mx] :
    Pr[= true | mx] + Pr[= false | mx] = 1 := by simp

omit [Monad m] in
@[simp, grind =]
lemma probEvent_true_eq_probOutput (mx : m Bool) :
    Pr[ (· = true) | mx] = Pr[= true | mx] := probEvent_eq_eq_probOutput mx true

omit [Monad m] in
@[simp, grind =]
lemma probEvent_not_eq_probOutput (mx : m Bool) :
    Pr[ (· = false) | mx] = Pr[= false | mx] := probEvent_eq_eq_probOutput mx false

lemma probOutput_true_bind_map_eq_probEvent [LawfulMonad m] [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : α → m β) (p : α → β → Bool) :
    Pr[= true | mx >>= fun x => p x <$> my x] =
      Pr[fun (x, y) => p x y | do let x ← mx; return (x, ← my x)] := by
  simp only [probOutput_bind_eq_tsum, probOutput_map_eq_tsum_ite, Bool.true_eq, bind_pure_comp,
    probEvent_bind_eq_tsum, probEvent_map]
  grind


