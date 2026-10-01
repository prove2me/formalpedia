-- Prove2me | Definitions.Def_Yukon_78fd002a26a9069876a24c31
-- name    : Yukon_78fd002a26a9069876a24c31
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:09.506824+00:00
-- url     : https://prove2.me/theorems/a1662eff-fd4d-4c73-8929-c16d17494ccc
-- title:
--   YukonModule.VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing.part0
-- statement:
--   Source module VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/HardnessAssumptions/EntropySmoothing.lean
--
--   yukon-proof-operation:5613e8e74627239fd93e60925b2dda4313c09199e0f7af2a9acec643c0874bf9
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NTYxM2U4ZTc0NjI3MjM5ZmQ5M2U2MDkyNWIyZGRhNDMxM2MwOTE5OWUwZjdhZjJhOWFjZWM2NDNjMDg3NGJmOSIsImhhc2giOiI4NThhMjI5NDUyZGNjNjI4ZTE0ZjYxYmMzMmE4M2RkMjBmMTU4NjUwYzAxZjkxODc3OTVjOWE3YTZiZGNjMDNhIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83OGZkMDAyYTI2YTkwNjk4NzZhMjRjMzEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee

public import Definitions.Def_Yukon_2b5744019605f484379c669d

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
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
meta import Definitions.Def_Yukon_3ca8dea642d23c4bd0e25cee
set_option backward.isDefEq.respectTransparency.types false
/-!
# Entropy Smoothing

This file defines the entropy-smoothing distinguishing game used by hashed ElGamal-style
constructions: the adversary distinguishes a real hash output `hash hk (z • g)` from an
independent uniform element of the output space.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace EntropySmoothing

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]
variable {HK : Type} [SampleableType HK]
variable {M : Type} [AddCommGroup M] [SampleableType M] [DecidableEq M]

/-- Real entropy-smoothing experiment. The adversary sees `(hk, hash hk (z • g))`
for uniform `hk` and `z`, and tries to distinguish this from the ideal experiment. -/
def realExp (g : G) (hash : HK → G → M) (adversary : HK × M → ProbComp Bool) :
    ProbComp Bool := do
  let hk ← $ᵗ HK
  let z ← $ᵗ F
  adversary (hk, hash hk (z • g))

/-- Ideal entropy-smoothing experiment. The adversary sees `(hk, h)` for independent
uniform `hk` and uniform `h : M`. -/
def idealExp (adversary : HK × M → ProbComp Bool) : ProbComp Bool := do
  let hk ← $ᵗ HK
  let h ← $ᵗ M
  adversary (hk, h)

/-- Entropy-smoothing distinguishing advantage. -/
noncomputable def advantage (g : G) (hash : HK → G → M)
    (adversary : HK × M → ProbComp Bool) : ℝ :=
  |(Pr[= true | realExp F g hash adversary]).toReal -
    (Pr[= true | idealExp adversary]).toReal|

end EntropySmoothing


