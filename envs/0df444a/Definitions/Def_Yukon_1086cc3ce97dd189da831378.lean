-- Prove2me | Definitions.Def_Yukon_1086cc3ce97dd189da831378
-- name    : Yukon_1086cc3ce97dd189da831378
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:59:29.646419+00:00
-- url     : https://prove2.me/theorems/b2876f7a-6533-430c-b337-ebd581bd0331
-- title:
--   YukonModule.VCVio.OracleComp.Coinductive.Bridge.part0
-- statement:
--   Source module VCVio.OracleComp.Coinductive.Bridge.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/Coinductive/Bridge.lean
--
--   yukon-proof-operation:a401d114991d764fc8d15c3edb4397a1e9f6c5391b09e152a8db2ce955737499
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YTQwMWQxMTQ5OTFkNzY0ZmM4ZDE1YzNlZGI0Mzk3YTFlOWY2YzUzOTFiMDllMTUyYThkYjJjZTk1NTczNzQ5OSIsImhhc2giOiI3NDk5MWJmNzIxZGI3MmQyNjY3YmQwOWJiOGFhODU1YTc0YmUxN2FjYjQwMTM1OWNlNTJkMDNmNTc1YzBkMDI5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8xMDg2Y2MzY2U5N2RkMTg5ZGE4MzEzNzgiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01

public import Definitions.Def_Yukon_8913aa8512f621542cbda9c9



public import Mathlib.Init
public import Init
public import Mathlib.Data.PFunctor.Univariate.M
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_8913aa8512f621542cbda9c9
meta import Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01
set_option backward.isDefEq.respectTransparency.types false
/-! # Bridge between `OracleComp` and `ITree`

`OracleComp spec α` is the *inductive* free monad on `spec.toPFunctor`;
`ITree spec.toPFunctor α` is the *coinductive* (M-type) free monad on the
same polynomial functor. Every finite, terminating `OracleComp` program has
a canonical embedding into the (potentially-infinite) ITree world.

This module provides that embedding, `OracleComp.toITree`, together with the
structural simp lemmas (`toITree_pure`, `toITree_queryBind`) that compute it.

The reverse map "ITree-to-OracleComp" exists *only* on terminating ITrees
and requires productivity / well-foundedness arguments that are not yet
in scope; hence we provide only the forward direction here.

## Universe restriction

To keep the polynomial functor uniform-universe, we specialise to
`OracleSpec.{u, u} ι`. The general `OracleSpec.{u, v}` case would force
`Poly F α` to live in `Type (max u v + 1)`, which is at odds with our
single-universe ITree definition.
-/

@[expose] public section

universe u

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-- Embed an `OracleComp spec α` into the corresponding `ITree`. Each `pure x`
becomes `ITree.pure x`; each `queryBind t k` becomes `ITree.query t (toITree ∘ k)`.
The recursion is structural on `OracleComp` (which is an inductive free monad),
so productivity is automatic. -/
def toITree (oa : OracleComp spec α) : ITree spec.toPFunctor α :=
  oa.recOn (motive := fun _ => ITree spec.toPFunctor α)
    ITree.pure
    (fun t _k ih => ITree.query (F := spec.toPFunctor) t ih)

@[simp] theorem toITree_pure (x : α) :
    toITree (pure x : OracleComp spec α) = ITree.pure x := rfl

@[simp] theorem toITree_queryBind (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    toITree (queryBind t k) = ITree.query (F := spec.toPFunctor) t (fun u => toITree (k u)) :=
  rfl

end OracleComp


