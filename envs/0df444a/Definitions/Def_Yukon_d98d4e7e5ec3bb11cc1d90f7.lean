-- Prove2me | Definitions.Def_Yukon_d98d4e7e5ec3bb11cc1d90f7
-- name    : Yukon_d98d4e7e5ec3bb11cc1d90f7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:17:21.158417+00:00
-- url     : https://prove2.me/theorems/a7615320-1b57-44a2-9b21-621f335d54d9
-- title:
--   YukonModule.VCVio.CryptoFoundations.HardnessAssumptions.HardRelation.part0
-- statement:
--   Source module VCVio.CryptoFoundations.HardnessAssumptions.HardRelation.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/HardnessAssumptions/HardRelation.lean
--
--   yukon-proof-operation:f292d0ee1c2a431915da9c907917c8cd955208059a57f829e91b5c5afda97c92
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjI5MmQwZWUxYzJhNDMxOTE1ZGE5YzkwNzkxN2M4Y2Q5NTUyMDgwNTlhNTdmODI5ZTkxYjVjNWFmZGE5N2M5MiIsImhhc2giOiJmMzgzMjA4YThlNGE4ZThmZjNlNjNhMzk1ZWNjY2RkYmQyMzhkOTJmYmVkOTVmM2Y3ZGFiMTgxOWVkNjkwODNkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kOThkNGU3ZTVlYzNiYjExY2MxZDkwZjciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee



public import Batteries.Control.OptionT
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
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
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Hard Relations

This file defines a typeclass `HardRelation X W r` for relations `r : X → W → Prop`
that are "hard" in the sense that given `x : X` no polynomial adversary can find `w : W`
such that `r x w` holds.

In the actual implementation all of these are indexed by some security parameter.

## Implementation notes

This is a simplified version without the asymptotic security parameter framework.
A full asymptotic version needs `OracleAlg` to be redesigned.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

/-- A relation `r` is generable if there is an efficient algorithm `gen`
that produces instance-witness pairs satisfying the relation. -/
structure GenerableRelation
    (X W : Type) (r : X → W → Bool) where
  /-- An efficient algorithm producing instance-witness pairs. -/
  gen : ProbComp (X × W)
  /-- Every pair in the support of `gen` satisfies the relation `r`. -/
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w

/-- Experiment for checking whether an adversary can find a witness for a generated instance. -/
def hardRelationExp {X W : Type} {r : X → W → Bool} (hr : GenerableRelation X W r)
    (adversary : X → ProbComp W) : ProbComp Bool := do
  let ⟨x, _⟩ ← hr.gen
  let w ← adversary x
  return r x w


