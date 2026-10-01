-- Prove2me | Definitions.Def_Yukon_e3fd5de4db781670631c9e44
-- name    : Yukon_e3fd5de4db781670631c9e44
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:17:09.735595+00:00
-- url     : https://prove2.me/theorems/d4e8c66c-c495-4726-bc9c-7aed3126ac7a
-- title:
--   YukonModule.VCVio.OracleComp.HasQuery.Morphism.part0
-- statement:
--   Source module VCVio.OracleComp.HasQuery.Morphism.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/HasQuery/Morphism.lean
--
--   yukon-proof-operation:99b7a606eaf776c8a651b52571ef1691dbeda482c09497b27eb67ad50691e2b3
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTliN2E2MDZlYWY3NzZjOGE2NTFiNTI1NzFlZjE2OTFkYmVkYTQ4MmMwOTQ5N2IyN2ViNjdhZDUwNjkxZTJiMyIsImhhc2giOiI5NDA4NzQ0YjhlZTY2MzY4NGYwMzYyZmJiY2Y4OTFiYjBkNDYyNDNlMGRmZjM3OWIyNmZkZmFlNTI5YTE1MWUwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9lM2ZkNWRlNGRiNzgxNjcwNjMxYzllNDQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Definitions.Def_Yukon_0c415a7ac30982e40294fe41

public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee

public import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b



public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.OptionT
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Batteries.Control.AlternativeMonad
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b
meta import Definitions.Def_Yukon_0c415a7ac30982e40294fe41
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Morphisms of `HasQuery` Monads

This module contains the heavier `HasQuery` naturality layer.
It imports `ProbComp` and monad homomorphisms, so files that only need the
basic query capability should import `VCVio.OracleComp.HasQuery.Basic`
instead.

Use this module for proofs that a monad morphism preserves oracle queries, or
that it commutes with the canonical lift of public randomness.
-/

@[expose] public section

universe u v w x

namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι}
  {m : Type v → Type w} [Monad m] [HasQuery spec m]
  {n : Type v → Type x} [Monad n] [HasQuery spec n]

/-- A `QueryHom spec m n` is a monad morphism `m →ᵐ n` that also preserves the distinguished
oracle-query capability for `spec`. This is the right notion of morphism for proving that a
construction generic over `HasQuery spec` is natural in the chosen oracle semantics. -/
structure QueryHom (spec : OracleSpec.{u, v} ι)
    (m : Type v → Type w) [Monad m] [HasQuery spec m]
    (n : Type v → Type x) [Monad n] [HasQuery spec n]
    extends m →ᵐ n where
  map_query' (t : spec.Domain) :
    toFun _ (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t

/-- A monad morphism preserves public randomness when it commutes with the distinguished lifting
of plain probabilistic computations into the ambient monad. -/
def PreservesProbCompLift
    {m : Type → Type w} [Monad m] [MonadLiftT ProbComp m]
    {n : Type → Type x} [Monad n] [MonadLiftT ProbComp n]
    (F : m →ᵐ n) : Prop :=
  ∀ {α : Type} (oa : ProbComp α), F (liftM oa : m α) = (liftM oa : n α)

@[simp]
lemma map_query (F : QueryHom spec m n) (t : spec.Domain) :
    F.toMonadHom (HasQuery.query (spec := spec) (m := m) t) =
      HasQuery.query (spec := spec) (m := n) t :=
  F.map_query' t

end HasQuery


