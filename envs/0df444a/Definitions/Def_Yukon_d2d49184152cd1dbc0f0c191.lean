-- Prove2me | Definitions.Def_Yukon_d2d49184152cd1dbc0f0c191
-- name    : Yukon_d2d49184152cd1dbc0f0c191
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:13.331823+00:00
-- url     : https://prove2.me/theorems/33f75840-b9de-4b42-8bb1-06656e626ef1
-- title:
--   YukonModule.VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.part0
-- statement:
--   Source module VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/HardnessAssumptions/MultiTarget.lean
--
--   yukon-proof-operation:f804d01dd16bbd882b0d210df4fb4287806b9bc33dece3d87918c3b14cda1aa1
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjgwNGQwMWRkMTZiYmQ4ODJiMGQyMTBkZjRmYjQyODc4MDZiOWJjMzNkZWNlM2Q4NzkxOGMzYjE0Y2RhMWFhMSIsImhhc2giOiJkM2MzMjA2MTlkNGU2MGY5NTc3M2JiMTdjMjQ4NDY0YTA5ZmY4MWNlMjIwN2Y3NmUwNWU4ZTk4YWZhOGRhZWIwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kMmQ0OTE4NDE1MmNkMWRiYzBmMGMxOTEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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
# Multi-Target Hash Assumptions (SM-PRE, SM-TCR)

The single-function multi-target preimage (SM-PRE) and target-collision (SM-TCR) resistance
notions that hash-based signatures such as SLH-DSA / SPHINCS+ reduce to. Unlike plain
one-wayness (`HardnessAssumptions.OneWay`) or collision resistance
(`HardnessAssumptions.CollisionResistance`), the SPHINCS+ analysis crucially uses
*single-function multi-target* hardness: the adversary is given `p` targets and wins by breaking
*any one* of them. The `p`-fold loss relative to the single-target notions is intended to be
recorded by separate bridge lemmas (future work), not baked into the advantage here.

The packaging mirrors `LatticeCrypto.HardnessAssumptions.ShortIntegerSolution` (the
`Problem`/`Adversary`/`experiment`/`advantage` shape). The assumptions are stated over plain
functions so that a (seed-fixed) `TweakableHash` can be plugged in.

## References

- Bernstein et al., SPHINCS+ (the multi-target preimage / target-collision treatment)
- Hülsing, Rijneveld, Song, Schwabe, "Mitigating Multi-Target Attacks in Hash-Based Signatures"
-/

@[expose] public section

open OracleComp ENNReal

namespace MultiTarget

/-! ### Single-function multi-target preimage resistance (SM-PRE) -/

/-- An SM-PRE problem for a fixed function `f : X → Y`: the challenger samples `numTargets`
preimages (via `sampleInputs`) and exposes their images; the adversary must invert one. -/
structure PreimageProblem (X Y : Type) where
  /-- The fixed function whose preimage resistance is in question. -/
  f : X → Y
  /-- The number of targets the adversary is challenged on. -/
  numTargets : ℕ
  /-- Sample all `numTargets` preimages at once. -/
  sampleInputs : ProbComp (Fin numTargets → X)

variable {X Y : Type}

/-- An SM-PRE adversary: given the `numTargets` images, return an index and a preimage. -/
structure PreimageAdversary (prob : PreimageProblem X Y) where
  /-- Given the target images, produce `(i, x')` aiming for `f x' = yᵢ`. -/
  run : (Fin prob.numTargets → Y) → ProbComp (Fin prob.numTargets × X)

/-- The SM-PRE experiment: sample the preimages, run the adversary on their images, and check
that the returned preimage hits the chosen target. -/
def preimageExperiment {prob : PreimageProblem X Y} [DecidableEq Y]
    (adv : PreimageAdversary prob) : ProbComp Bool := do
  let xs ← prob.sampleInputs
  let (i, x') ← adv.run fun i => prob.f (xs i)
  return decide (prob.f x' = prob.f (xs i))

/-- The SM-PRE advantage of an adversary. -/
noncomputable def preimageAdvantage {prob : PreimageProblem X Y} [DecidableEq Y]
    (adv : PreimageAdversary prob) : ℝ≥0∞ :=
  Pr[= true | preimageExperiment adv]

/-! ### Single-function multi-target target-collision resistance (SM-TCR) -/

/-- An SM-TCR problem for a fixed tweakable function `f : Tweak → M → Y`: the adversary commits
`numTargets` target pairs `(tweak, message)`, then must find, for one of them, a *different*
message hashing (under the same tweak) to the same value. -/
structure TcrProblem (Tweak M Y : Type) where
  /-- The fixed tweakable function whose target-collision resistance is in question. -/
  f : Tweak → M → Y
  /-- The number of targets the adversary commits to. -/
  numTargets : ℕ

variable {Tweak M Y : Type}

/-- An SM-TCR adversary: a `choose` phase committing the target `(tweak, message)` pairs (with
private state), and a `forge` phase producing a colliding message for one committed target. -/
structure TcrAdversary (prob : TcrProblem Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Commit the `numTargets` target `(tweak, message)` pairs. -/
  choose : ProbComp ((Fin prob.numTargets → Tweak × M) × State)
  /-- Given the committed targets' hash values, produce `(j, m')` aiming for a collision at
  target `j`. -/
  forge : State → (Fin prob.numTargets → Y) → ProbComp (Fin prob.numTargets × M)

/-- The SM-TCR experiment: commit the targets, run the forge phase on their hashes, and check
that the forged message differs from the committed one yet collides under the same tweak. -/
def tcrExperiment {prob : TcrProblem Tweak M Y} [DecidableEq M] [DecidableEq Y]
    (adv : TcrAdversary prob) : ProbComp Bool := do
  let (targets, st) ← adv.choose
  let (j, m') ← adv.forge st fun i => prob.f (targets i).1 (targets i).2
  let (tweak, m) := targets j
  return decide (m' ≠ m ∧ prob.f tweak m' = prob.f tweak m)

/-- The SM-TCR advantage of an adversary. -/
noncomputable def tcrAdvantage {prob : TcrProblem Tweak M Y} [DecidableEq M] [DecidableEq Y]
    (adv : TcrAdversary prob) : ℝ≥0∞ :=
  Pr[= true | tcrExperiment adv]

end MultiTarget


