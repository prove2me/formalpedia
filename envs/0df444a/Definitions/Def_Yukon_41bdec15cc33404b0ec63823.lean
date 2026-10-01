-- Prove2me | Definitions.Def_Yukon_41bdec15cc33404b0ec63823
-- name    : Yukon_41bdec15cc33404b0ec63823
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:46.58372+00:00
-- url     : https://prove2.me/theorems/79e20a8e-8888-4f4d-8984-aaf92f9928fd
-- title:
--   YukonModule.VCVio.EvalDist.Fintype.part0
-- statement:
--   Source module VCVio.EvalDist.Fintype.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/Fintype.lean
--
--   yukon-proof-operation:343b135eaf6f971d9f0d2ea452a4dca3a7f893c05a4269d68e4791505b5004ba
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzQzYjEzNWVhZjZmOTcxZDlmMGQyZWE0NTJhNGRjYTNhN2Y4OTNjMDVhNDI2OWQ2OGU0NzkxNTA1YjUwMDRiYSIsImhhc2giOiJjOWFmNGZjMzFmZmRkYjFkMDIyZGE1Mzc3NWQ2NjM4MWZiYzY5OTllMzBhZWI0OTQ0OTNhNjVjMmNiNDAxMjRkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl80MWJkZWMxNWNjMzM0MDRiMGVjNjM4MjMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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
meta import Definitions.Def_Yukon_10be02bf5325c192ea9b6156
set_option backward.isDefEq.respectTransparency.types false
/-!
# Lemmas for Probability Over Finite Spaces

This file houses lemmas about computations with `MonadLiftT m SPMF` semantics when
`mx : m α` is defined via a binding/mapping operation over a finite type.
In particular it provides `Finset.sum` versions of many `tsum` related probability lemmas.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

lemma probOutput_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : α → m β) [Fintype α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x : α, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_fintype _)

lemma probFailure_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : α → m β) [Fintype α] :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑ x : α, Pr[= x | mx] * Pr[⊥ | my x] :=
  (probFailure_bind_eq_add_tsum mx my).trans (congr_arg (Pr[⊥ | mx] + ·) <| tsum_fintype _)

lemma probEvent_bind_eq_sum_fintype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : α → m β) [Fintype α] (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑ x : α, Pr[= x | mx] * Pr[ q | my x] :=
  (probEvent_bind_eq_tsum mx my q).trans (tsum_fintype _)


