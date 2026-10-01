-- Prove2me | Definitions.Def_Yukon_548e569f5946909e0d9a91e1
-- name    : Yukon_548e569f5946909e0d9a91e1
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:23.088608+00:00
-- url     : https://prove2.me/theorems/478a62f6-d53a-4950-af99-3a31ed68e391
-- title:
--   YukonModule.VCVio.CryptoFoundations.CommitmentScheme.part0
-- statement:
--   Source module VCVio.CryptoFoundations.CommitmentScheme.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/CommitmentScheme.lean
--
--   yukon-proof-operation:4c734b3fd42a9da0b4efe2c6ce7ea1dbfe18ae4c231af71889a7b626b22e6b5f
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NGM3MzRiM2ZkNDJhOWRhMGI0ZWZlMmM2Y2U3ZWExZGJmZTE4YWU0YzIzMWFmNzE4ODlhN2I2MjZiMjJlNmI1ZiIsImhhc2giOiIwN2QxNGYxZjM0MWY5NjAwZGM0ODViY2YzN2IwMmM5MTczMWFmOWY5OTZlNzc5MjZjMTkyZDUwZWM1YTE5ZmNmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl81NDhlNTY5ZjU5NDY5MDllMGQ5YTkxZTEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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
# Commitment Schemes

This file defines non-interactive commitment schemes and their standard security
properties: correctness, hiding, and binding.

## Main Definitions

- `CommitmentScheme PP M C D` — a commitment scheme with public parameters `PP`,
  message space `M`, commitment space `C`, and opening (decommitment) space `D`.
- `CommitmentScheme.PerfectlyCorrect` — honestly generated parameters and commitments always
  verify.
- `CommitmentScheme.PerfectlyHiding` — under honestly generated parameters, commitment
  distribution is independent of the message.
- `CommitmentScheme.hidingExp` — computational hiding experiment (IND-style).
- `CommitmentScheme.bindingExp` — computational binding experiment.
- `TrapdoorExtractor PP TD C M` — trapdoor-based message extraction algorithm.
- `CommitmentScheme.extractExp` — extraction experiment (game-based, allows error).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-- A non-interactive commitment scheme with public parameters `PP`, message space `M`,
commitment space `C`, and opening (decommitment) space `D`. -/
structure CommitmentScheme (PP M C D : Type) where
  /-- Generate public parameters (e.g. a common reference string). -/
  setup : ProbComp PP
  /-- Commit to a message, producing a commitment and an opening. -/
  commit (pp : PP) (m : M) : ProbComp (C × D)
  /-- Deterministic verification that an opening is valid. -/
  verify (pp : PP) (m : M) (c : C) (d : D) : Bool

namespace CommitmentScheme

variable {PP M C D : Type}

/-- A commitment scheme is perfectly correct if every honestly generated public
parameter and commitment-opening pair passes verification. -/
def PerfectlyCorrect (cs : CommitmentScheme PP M C D) : Prop :=
  ∀ pp, pp ∈ support cs.setup →
    ∀ m cd, cd ∈ support (cs.commit pp m) → cs.verify pp m cd.1 cd.2 = true

/-- A commitment scheme is perfectly hiding if, for every honestly generated
public parameter, the commitment (first component) has the same distribution
regardless of the committed message. -/
def PerfectlyHiding (cs : CommitmentScheme PP M C D) : Prop :=
  ∀ pp, pp ∈ support cs.setup →
    ∀ m₁ m₂, 𝒟[Prod.fst <$> cs.commit pp m₁] =
      𝒟[Prod.fst <$> cs.commit pp m₂]

/-! ### Computational hiding -/

/-- A two-phase hiding adversary: phase 1 chooses two messages given the public parameters;
phase 2 receives the commitment and tries to guess which message was committed.
`State` carries information between the two phases. -/
structure HidingAdv (PP M C : Type) where
  State : Type
  chooseMessages : PP → ProbComp (M × M × State)
  distinguish : State → C → ProbComp Bool

/-- Hiding experiment: the adversary chooses two messages, the challenger commits
to one at random, and the adversary tries to guess which. -/
def hidingExp (cs : CommitmentScheme PP M C D) (adversary : HidingAdv PP M C) : ProbComp Bool := do
  let pp ← cs.setup
  let (m₁, m₂, st) ← adversary.chooseMessages pp
  let b ← $ᵗ Bool
  let (c, _) ← cs.commit pp (if b then m₁ else m₂)
  let b' ← adversary.distinguish st c
  return (b == b')

/-- The hiding advantage of an adversary: how far its winning probability in `hidingExp`
deviates from the `1 / 2` of a random guess. -/
noncomputable def hidingAdvantage (cs : CommitmentScheme PP M C D) (adversary : HidingAdv PP M C) :
    ℝ :=
  |(Pr[= true | cs.hidingExp adversary]).toReal - 1 / 2|

/-! ### Computational binding -/

/-- A binding adversary outputs a commitment with two openings to different messages. -/
def BindingAdv (PP M C D : Type) := PP → ProbComp (C × M × D × M × D)

/-- Binding experiment: the adversary tries to open a single commitment to two
distinct messages. Succeeds iff both openings verify and the messages differ. -/
def bindingExp [DecidableEq M] (cs : CommitmentScheme PP M C D) (adversary : BindingAdv PP M C D) :
    ProbComp Bool := do
  let pp ← cs.setup
  let (c, m₁, d₁, m₂, d₂) ← adversary pp
  return (decide (m₁ ≠ m₂) && cs.verify pp m₁ c d₁ && cs.verify pp m₂ c d₂)

/-- The binding advantage of an adversary: its probability of winning `bindingExp` by
opening a single commitment to two distinct messages. -/
noncomputable def bindingAdvantage [DecidableEq M] (cs : CommitmentScheme PP M C D)
    (adversary : BindingAdv PP M C D) : ℝ≥0∞ :=
  Pr[= true | cs.bindingExp adversary]

/-! ### Trapdoor extractability -/

/-- A trapdoor extractor for a commitment scheme: bundles an alternative setup
that produces a trapdoor alongside the public parameters, and a (potentially
probabilistic) extraction algorithm that recovers the committed message from
the commitment using the trapdoor.

Named `TrapdoorExtractor` specifically to leave room for other extraction
paradigms (e.g. rewinding-based extraction). -/
structure TrapdoorExtractor (PP TD C M : Type) where
  setupExtract : ProbComp (PP × TD)
  extract : TD → C → ProbComp M

/-- The extraction setup produces the same public parameter distribution as
the scheme's normal setup. Required for reductions that swap in the
trapdoor setup without the adversary noticing. -/
def TrapdoorExtractor.SetupConsistent {TD : Type} (extractor : TrapdoorExtractor PP TD C M)
    (cs : CommitmentScheme PP M C D) : Prop :=
  𝒟[Prod.fst <$> extractor.setupExtract] = 𝒟[cs.setup]

/-- Extraction experiment: generate parameters with trapdoor, honestly commit
to message `m`, then check whether the extractor recovers `m` from the commitment.

Downstream code decides how much error to tolerate:
- Perfect extraction: `∀ m, Pr[= true | extractExp cs ext m] = 1`
- Computational: bound `1 - Pr[= true | extractExp cs ext m]` -/
def extractExp [DecidableEq M] (cs : CommitmentScheme PP M C D) {TD : Type}
    (extractor : TrapdoorExtractor PP TD C M) (m : M) : ProbComp Bool := do
  let (pp, td) ← extractor.setupExtract
  let (c, _) ← cs.commit pp m
  let m' ← extractor.extract td c
  return decide (m' = m)

end CommitmentScheme


