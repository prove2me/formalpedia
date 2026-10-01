-- Prove2me | Definitions.Def_Yukon_92db958debc53176a8bcb5d5
-- name    : Yukon_92db958debc53176a8bcb5d5
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:21.190988+00:00
-- url     : https://prove2.me/theorems/d5083c88-0f4e-44a2-91e9-2200068c798e
-- title:
--   YukonModule.VCVio.CryptoFoundations.HardnessAssumptions.OneWay.part0
-- statement:
--   Source module VCVio.CryptoFoundations.HardnessAssumptions.OneWay.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/HardnessAssumptions/OneWay.lean
--
--   yukon-proof-operation:c38bd8a83a67341a7a91c838521428337a1d02fd9339dd9ab24d892685ee73db
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YzM4YmQ4YTgzYTY3MzQxYTdhOTFjODM4NTIxNDI4MzM3YTFkMDJmZDkzMzlkZDlhYjI0ZDg5MjY4NWVlNzNkYiIsImhhc2giOiJkODM5Yjc2YzMxYmRkYzIyNWIyODBjNTkyMmUxMjRkNGVlNWViZDE3NDk0YWQ4MDkyZTMxNDA5MDg1N2I0OWNjIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85MmRiOTU4ZGViYzUzMTc2YThiY2I1ZDUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7

public import Definitions.Def_Yukon_2b5744019605f484379c669d

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
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# One-Way Functions and Trapdoor Permutations

This file defines one-way functions (OWFs) and one-way trapdoor permutations (OW-TDPs),
along with their security experiments.

## One-Way Functions

A function `f : X → Y` is one-way if no efficient adversary, given `f(x)` for a random `x`,
can find any preimage `x'` with `f(x') = f(x)`.

## Trapdoor Permutations

A trapdoor permutation has a key generation algorithm that produces a public key `pk`
and a secret key `sk`. The forward direction `f(pk, ·)` is a permutation that is hard to
invert given only `pk`; the secret key enables efficient inversion via `f⁻¹(sk, ·)`.

## Main Definitions

- `OWFAdversary X Y` — an adversary trying to invert `f`.
- `owfExp` — the one-wayness experiment.
- `TrapdoorPermutation PK SK X` — a trapdoor permutation scheme.
- `TDPAdversary PK X` — an adversary trying to invert the TDP.
- `tdpExp` — the TDP inversion experiment.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace OneWay

variable {X Y : Type}

/-! ## One-Way Functions -/

/-- An OWF adversary receives `f(x)` and tries to find a preimage. -/
def OWFAdversary (X Y : Type) := Y → ProbComp X

/-- One-wayness experiment: sample `x` uniformly, give the adversary `f(x)`,
and check whether the adversary's output is a valid preimage. -/
def owfExp [SampleableType X] [DecidableEq Y] (f : X → Y) (adversary : OWFAdversary X Y) :
    ProbComp Bool := do
  let x ← $ᵗ X
  let x' ← adversary (f x)
  return decide (f x' = f x)

/-- OWF advantage: the probability of successfully inverting `f`. -/
noncomputable def owfAdvantage [SampleableType X] [DecidableEq Y] (f : X → Y)
    (adversary : OWFAdversary X Y) : ℝ≥0∞ :=
  Pr[= true | owfExp f adversary]

/-! ## Trapdoor Permutations -/

variable {PK SK : Type}

/-- A trapdoor permutation with key spaces `PK`/`SK` and domain `X`.
The forward direction is a permutation computable from the public key;
the inverse requires the secret key (the trapdoor). -/
structure TrapdoorPermutation (PK SK X : Type) where
  keygen : ProbComp (PK × SK)
  forward : PK → X → X
  inverse : SK → X → X

/-- A trapdoor permutation is correct if inversion recovers the original input
for all honestly generated key pairs. -/
def TrapdoorPermutation.Correct (tdp : TrapdoorPermutation PK SK X) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support tdp.keygen →
    ∀ x, tdp.inverse sk (tdp.forward pk x) = x

/-- A TDP adversary receives the public key and a challenge `y = f(pk, x)`,
and tries to find a valid preimage of `y`. -/
def TDPAdversary (PK X : Type) := PK → X → ProbComp X

/-- TDP inversion experiment: generate keys, sample `x` uniformly,
and check whether the adversary outputs a valid preimage of `f(pk, x)`. -/
def tdpExp [SampleableType X] [DecidableEq X] (tdp : TrapdoorPermutation PK SK X)
    (adversary : TDPAdversary PK X) : ProbComp Bool := do
  let (pk, _) ← tdp.keygen
  let x ← $ᵗ X
  let x' ← adversary pk (tdp.forward pk x)
  return decide (tdp.forward pk x' = tdp.forward pk x)

/-- TDP advantage: the probability of successfully producing a valid preimage
without the trapdoor. -/
noncomputable def tdpAdvantage [SampleableType X] [DecidableEq X]
    (tdp : TrapdoorPermutation PK SK X) (adversary : TDPAdversary PK X) : ℝ≥0∞ :=
  Pr[= true | tdpExp tdp adversary]

end OneWay


