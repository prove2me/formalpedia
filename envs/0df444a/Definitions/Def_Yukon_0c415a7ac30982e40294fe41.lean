-- Prove2me | Definitions.Def_Yukon_0c415a7ac30982e40294fe41
-- name    : Yukon_0c415a7ac30982e40294fe41
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:59:42.989726+00:00
-- url     : https://prove2.me/theorems/4e3ab493-fe77-4a75-9152-27274f768c73
-- title:
--   YukonModule.VCVio.OracleComp.HasQuery.Basic.part0
-- statement:
--   Source module VCVio.OracleComp.HasQuery.Basic.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/HasQuery/Basic.lean
--
--   yukon-proof-operation:be95a7ad46065480c5df3da79bceae686838ea6889c7a00035d1ae9d74eef15e
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YmU5NWE3YWQ0NjA2NTQ4MGM1ZGYzZGE3OWJjZWFlNjg2ODM4ZWE2ODg5YzdhMDAwMzVkMWFlOWQ3NGVlZjE1ZSIsImhhc2giOiI2NDFhYzY1NTcyZjFmMWI0OTJlNjhiNzRjNmQyNjgzMDNhNmY2NGU4NTA4ODRkMzhjNGE3YjhhMDBiZmY3NDQ2Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wYzQxNWE3YWMzMDk4MmU0MDI5NGZlNDEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Definitions.Def_Yukon_135b1e0f495a7a36531945f6



public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
meta import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
set_option backward.isDefEq.respectTransparency.types false
/-!
# Basic `HasQuery` Capability

This is the lightweight dependency boundary for the query capability.
It defines `HasQuery spec m`, exports the bare identifier `query`, and provides
only the foundational instances for primitive query syntax and monad lifts.

Core syntax modules, especially `VCVio.OracleComp.OracleComp`, should import
this file when they need the class or the bare `query` export.
Do not add `QueryImpl`, `ProbComp`, or monad-morphism APIs here; those live in
downstream modules with explicit imports.
-/

@[expose] public section

universe u v w

/-- Capability to issue queries to the oracle family `spec` inside the ambient monad `m`. -/
class HasQuery {ι : Type u} (spec : OracleSpec.{u, v} ι) (m : Type v → Type w) where
  /-- Issue a single oracle query. -/
  query : (t : spec.Domain) → m (spec.Range t)

-- Re-export `HasQuery.query` as the bare identifier `query`. With
-- `OracleSpec.query` marked `protected`, the bare `query` resolves to
-- `HasQuery.query`, which yields a value in the ambient monad `m` and lets
-- Lean recover `spec` from the expected return type.
export HasQuery (query)

namespace HasQuery

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {m : Type v → Type w}

/-- The primitive single-query syntax `OracleQuery spec` has the obvious query capability. -/
instance instOracleQuery : HasQuery spec (OracleQuery spec) where
  query := OracleSpec.query

@[simp]
lemma instOracleQuery_query (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := OracleQuery spec) t =
      OracleSpec.query t :=
  rfl

/-- Any lawful lift of `OracleQuery spec` into `m` gives query capability in `m`. This is the
main bridge that makes `HasQuery` compose with `SubSpec` lifts and standard transformer lifts. -/
instance (priority := low) instOfMonadLift [MonadLiftT (OracleQuery spec) m] :
    HasQuery spec m where
  query t := liftM (OracleSpec.query t)

@[simp]
lemma instOfMonadLift_query [MonadLiftT (OracleQuery spec) m] (t : spec.Domain) :
    HasQuery.query (spec := spec) (m := m) t =
      liftM (OracleSpec.query t) :=
  rfl

end HasQuery


