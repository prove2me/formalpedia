-- Prove2me | Definitions.Def_Yukon_cda3959af6f436acfe6b2dff
-- name    : Yukon_cda3959af6f436acfe6b2dff
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:43.605155+00:00
-- url     : https://prove2.me/theorems/b4df3975-3da8-4da4-9d20-4de5f7538b7f
-- title:
--   YukonModule.VCVio.EvalDist.BitVec.part0
-- statement:
--   Source module VCVio.EvalDist.BitVec.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/EvalDist/BitVec.lean
--
--   yukon-proof-operation:b7a9132ddc8f53774c06a519ec5010a529646b2d45a57c9524c0f504cfda6aab
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YjdhOTEzMmRkYzhmNTM3NzRjMDZhNTE5ZWM1MDEwYTUyOTY0NmIyZDQ1YTU3Yzk1MjRjMGY1MDRjZmRhNmFhYiIsImhhc2giOiI5MmVkMTliMzlkNDA3OGFjZjI0MTlkNWJhY2Q3ZWRhNzI4NTc1MDdiMDIwNmJhNDM3MWQwODU3MzFmNmIyNTdhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jZGEzOTU5YWY2ZjQzNmFjZmU2YjJkZmYiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
meta import Definitions.Def_Yukon_bb6a74fb27943bb3c66baf5c
set_option backward.isDefEq.respectTransparency.types false
/-!
# Evaluation Distributions of Computations with `BitVec`

Lemmas about `probOutput` involving `BitVec`, generic over any monad `m` with `[MonadLiftT m SPMF]`.

The `SampleableType (BitVec n)` instance is defined in
`VCVio.OracleComp.Constructions.SampleableType`.
-/

@[expose] public section

open BitVec

variable {α β γ : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]

@[simp, grind =]
lemma probOutput_ofFin_map {n : ℕ} (mx : m (Fin (2 ^ n))) (x : BitVec n) :
    Pr[= x | ofFin <$> mx] = Pr[= toFin x | mx] := by aesop

@[simp, grind =]
lemma probOutput_bitVec_toFin_map {n : ℕ} (mx : m (BitVec n)) (x : Fin (2 ^ n)) :
    Pr[= x | toFin <$> mx] = Pr[= ofFin x | mx] := by aesop

omit [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] in
@[simp]
lemma probOutput_xor_map {n : ℕ} (mx : m (BitVec n)) (x y : BitVec n) :
    Pr[= y | (x ^^^ ·) <$> mx] = Pr[= x ^^^ y | mx] := by
  have hinj : Function.Injective (x ^^^ ·) := fun a b h => by simpa using congrArg (x ^^^ ·) h
  conv_lhs => rw [show y = x ^^^ (x ^^^ y) by simp]
  exact probOutput_map_injective mx hinj (x ^^^ y)


