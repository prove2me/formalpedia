-- Prove2me | Definitions.Def_Yukon_55d30d3deeb7817ce41e3794
-- name    : Yukon_55d30d3deeb7817ce41e3794
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:17:28.737981+00:00
-- url     : https://prove2.me/theorems/36a4e403-9580-4e15-ae47-a69a8ae7c40e
-- title:
--   YukonModule.VCVio.OracleComp.ProbCompLift.part0
-- statement:
--   Source module VCVio.OracleComp.ProbCompLift.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/ProbCompLift.lean
--
--   yukon-proof-operation:608089938caa24a26d9d98be3fbbdbd5e6cc5154fb0c322bce28fbc267a30722
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjA4MDg5OTM4Y2FhMjRhMjZkOWQ5OGJlM2ZiYmRiZDVlNmNjNTE1NGZiMGMzMjJiY2UyOGZiYzI2N2EzMDcyMiIsImhhc2giOiI2NDZmMTdiNzkzMjc5YWY4YjAwMTFjOThkMzA1NzllZmVjOTcwNDJjMTNhMjViNTgwZmEwMWVkZDExNmQ0NWMxIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl81NWQzMGQzZGVlYjc4MTdjZTQxZTM3OTQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee

public import Definitions.Def_Yukon_d24a38ec5f10307fd0342f04

public import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b



public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Init
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Batteries.Control.AlternativeMonad
public import Batteries.Control.OptionT
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
meta import Definitions.Def_Yukon_d24a38ec5f10307fd0342f04
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Bundled Lifts from `ProbComp`

This file packages the "public randomness" capability separately from denotational semantics.

Many crypto constructions need two orthogonal pieces of structure on their ambient monad `m`:

1. a way to *observe* computations probabilistically (`SPMFSemantics` / `PMFSemantics`)
2. a way to *inject* plain probabilistic sampling into `m`

This file packages the second capability as a bundled monad homomorphism `ProbComp →ᵐ m`, so it
can be carried independently of whatever denotational semantics the construction uses. It also
defines `ProbCompRuntime`, the common crypto-facing bundle that pairs public-randomness lifting
with bundled `SPMF` semantics for an ambient monad.
-/

@[expose] public section

universe v w

/-- Bundled way to lift plain probabilistic computations into an ambient monad `m`.

Intuitively, this is the capability "sample fresh public randomness inside `m`". We package it as
a monad homomorphism so it composes lawfully with `pure` and `bind`. -/
structure ProbCompLift (m : Type → Type v) [Monad m] where
  /-- Inject a plain `ProbComp` computation into `m`. -/
  liftProbComp : ProbComp →ᵐ m

namespace ProbCompLift

/-- Build a bundled `ProbCompLift` from an existing lawful `MonadLiftT ProbComp m` instance. -/
def ofMonadLift (m : Type → Type v) [Monad m]
    [MonadLiftT ProbComp m] [LawfulMonadLiftT ProbComp m] : ProbCompLift m where
  liftProbComp := MonadHom.ofLift ProbComp m

/-- The identity lift on `ProbComp` itself. -/
def id : ProbCompLift ProbComp where
  liftProbComp := MonadHom.id ProbComp

end ProbCompLift

/-- Common runtime bundle for crypto games in an ambient monad `m`.

This packages the two capabilities that security experiments usually need together:

1. `SPMFSemantics m` to observe the experiment as a Boolean subdistribution.
2. `ProbCompLift m` to sample fresh public randomness inside `m`.

The bundle is kept separate from the core scheme definitions so that executable scheme data does
not become noncomputable merely by carrying denotational semantics. -/
structure ProbCompRuntime (m : Type → Type v) [Monad m] where
  /-- Bundled subprobabilistic semantics for the ambient monad. -/
  toSPMFSemantics : SPMFSemantics.{0, v, w} m
  /-- Bundled injection of plain probabilistic sampling into the ambient monad. -/
  toProbCompLift : ProbCompLift m

namespace ProbCompRuntime

variable {m : Type → Type v} [Monad m] {α : Type}

/-- Observe an ambient computation as an `SPMF` using the runtime's bundled semantics. -/
def evalDist (runtime : ProbCompRuntime m) (mx : m α) : SPMF α :=
  runtime.toSPMFSemantics.evalDist mx

/-- Failure probability of an ambient computation under the runtime's bundled semantics. -/
def probFailure (runtime : ProbCompRuntime m) (mx : m α) : ENNReal :=
  runtime.toSPMFSemantics.probFailure mx

/-- Lift a plain `ProbComp` computation into the ambient monad using the runtime's public
randomness capability. -/
def liftProbComp (runtime : ProbCompRuntime m) : ProbComp →ᵐ m :=
  runtime.toProbCompLift.liftProbComp

/-- Canonical runtime for `ProbComp` itself. -/
noncomputable def probComp : ProbCompRuntime ProbComp where
  toSPMFSemantics := SPMFSemantics.ofMonadLift ProbComp
  toProbCompLift := ProbCompLift.id

end ProbCompRuntime


