-- Prove2me | Definitions.Def_Yukon_9d723aac7b391c205a909f63
-- name    : Yukon_9d723aac7b391c205a909f63
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:27.45785+00:00
-- url     : https://prove2.me/theorems/26de1bd8-e765-455c-b080-1fe122861d57
-- title:
--   YukonModule.VCVio.CryptoFoundations.TweakableHash.part0
-- statement:
--   Source module VCVio.CryptoFoundations.TweakableHash.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/TweakableHash.lean
--
--   yukon-proof-operation:bf5dccbb2e44d13947dc3067e62645fb6bf2f8380f6d22063d9ad8cb2842ac7c
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YmY1ZGNjYmIyZTQ0ZDEzOTQ3ZGMzMDY3ZTYyNjQ1ZmI2YmYyZjgzODBmNmQyMjA2M2Q5YWQ4Y2IyODQyYWM3YyIsImhhc2giOiJiYmE5N2Q1MzM3YmRkMjVjZTIwODQxMmU5NDNhMmRmODYwM2FiNDVlZTFlZGZmM2Q1YzQwODNhMGU1MmE0Njg1Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85ZDcyM2FhYzdiMzkxYzIwNWE5MDlmNjMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee

public import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7



public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
public import Init
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Vector.Defs
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
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
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Tweakable Hash Families

A tweakable hash family `Th : PkSeed → Tweak → M → Y` generalizes `KeyedHashFamily` by
splitting the key into a *sampled* public seed and a *caller-supplied* abstract tweak. It is the
abstraction that the SLH-DSA / SPHINCS+ functions `F`, `H`, and `T_ℓ` instantiate (with the
tweak being the 32-byte address `ADRS`), and against which their multi-target security notions
(`VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget`) are stated.

This file provides the data abstraction only; the security games live in `MultiTarget` and are
deliberately stated over plain functions `X → Y` / `Tweak → M → Y`, so a partially-applied
tweakable hash can be fed in without a circular dependency.

With `Tweak := Unit` this is definitionally a keyed hash family
(`seedGen : ProbComp PkSeed`, `eval : PkSeed → M → Y`), so nothing is lost relative to the
existing `KeyedHashFamily` surface.
-/

@[expose] public section

open OracleComp

/-- A tweakable hash family: a sampled public seed plus a deterministic evaluation taking a
public seed, a tweak, and a message to a digest. -/
structure TweakableHash (PkSeed Tweak M Y : Type) where
  /-- Sample the public seed `PK.seed`. -/
  seedGen : ProbComp PkSeed
  /-- Evaluate the tweakable hash at a public seed, tweak, and message. -/
  eval : PkSeed → Tweak → M → Y

namespace TweakableHash

variable {PkSeed Tweak Y : Type}

/-- The two-input node hash `(left ‖ right) ↦ digest` at a fixed seed and tweak, as used to
combine sibling nodes in a Merkle tree. -/
def nodeHash (th : TweakableHash PkSeed Tweak (Y × Y) Y) (pk : PkSeed) (t : Tweak)
    (l r : Y) : Y :=
  th.eval pk t (l, r)

end TweakableHash


