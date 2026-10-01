-- Prove2me | Definitions.Def_Yukon_c572cdc7ac754cf2a006a2e7
-- name    : Yukon_c572cdc7ac754cf2a006a2e7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:01:39.886089+00:00
-- url     : https://prove2.me/theorems/1db0b126-3573-4c62-bcc9-3c7cbe7b2996
-- title:
--   YukonModule.VCVio.OracleComp.SimSemantics.ReaderT.Basic.part0
-- statement:
--   Source module VCVio.OracleComp.SimSemantics.ReaderT.Basic.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/SimSemantics/ReaderT/Basic.lean
--
--   yukon-proof-operation:f126f6a0955ce536f6437df0b1122b12e7844d118bd78b54040b5465749fec58
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjEyNmY2YTA5NTVjZTUzNmY2NDM3ZGYwYjExMjJiMTJlNzg0NGQxMThiZDc4YjU0MDQwYjU0NjU3NDlmZWM1OCIsImhhc2giOiIwYWE1YTY0MWI4YTBhYzNhMWMwYTJlMWQxNzRiMmQ4YTFkYjI4MzBmNDY2MGMyMGE1ZWNkY2FmNTJhYTc4ZTQ3Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jNTcyY2RjN2FjNzU0Y2YyYTAwNmEyZTciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_dcb7ae1acc5c3f644cb2dbde



public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_dcb7ae1acc5c3f644cb2dbde
set_option backward.isDefEq.respectTransparency.types false
/-!
# Query Implementations with Reader Monads

This file gives lemmas about `QueryImpl spec m` when `m` is something like `ReaderT ρ n`.

TODO: should generalize things to `MonadReader` once laws for it exist.
-/

@[expose] public section

universe u v w x

open OracleSpec

namespace QueryImpl

/-- Given implementations for oracles in `spec₁` and `spec₂` in terms of reader monads for
two different contexts `ρ₁` and `ρ₂`, implement the combined set `spec₁ + spec₂` in terms
of a combined `ρ₁ × ρ₂` state. The binary analogue of `QueryImpl.sigmaReaderT`. -/
def addReaderT {ι₁ : Type u} {ι₂ : Type v}
    {spec₁ : OracleSpec.{u, w} ι₁} {spec₂ : OracleSpec.{v, w} ι₂}
    {m : Type w → Type x} {ρ₁ ρ₂ : Type w}
    (impl₁ : QueryImpl spec₁ (ReaderT ρ₁ m))
    (impl₂ : QueryImpl spec₂ (ReaderT ρ₂ m)) :
    QueryImpl (spec₁ + spec₂) (ReaderT (ρ₁ × ρ₂) m)
  | .inl t => ReaderT.mk fun s => (impl₁ t).run s.1
  | .inr t => ReaderT.mk fun s => (impl₂ t).run s.2

/-- Indexed version of `QueryImpl.addReaderT`. Each query for index `t` reads from the
`t`-th component of the pi-product `(t : τ) → ρ t`. Note that `m` cannot vary with `t`. -/
def sigmaReaderT {τ : Type} {ι : τ → Type _}
    {spec : (t : τ) → OracleSpec (ι t)}
    {m : Type _ → Type _} {ρ : τ → Type _}
    (impl : (t : τ) → QueryImpl (spec t) (ReaderT (ρ t) m)) :
    QueryImpl (OracleSpec.sigma spec) (ReaderT ((t : τ) → ρ t) m)
  | ⟨t, q⟩ => ReaderT.mk fun s => (impl t q).run (s t)

/-- Reassociate a nested reader transformer into one product context.

The outer context is the first component of the product; the inner/base context is the
second. This is the reader-transformer analogue of `flattenStateT` and `flattenWriterT`. -/
def flattenReaderT {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {m : Type v → Type w} {ρ₁ ρ₂ : Type v}
    (impl : QueryImpl spec (ReaderT ρ₁ (ReaderT ρ₂ m))) :
    QueryImpl spec (ReaderT (ρ₁ × ρ₂) m) := fun t =>
  ReaderT.mk fun (r₁, r₂) => ((impl t).run r₁).run r₂

end QueryImpl


