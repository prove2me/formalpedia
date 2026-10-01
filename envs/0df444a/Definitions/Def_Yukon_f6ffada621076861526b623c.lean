-- Prove2me | Definitions.Def_Yukon_f6ffada621076861526b623c
-- name    : Yukon_f6ffada621076861526b623c
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:07.130988+00:00
-- url     : https://prove2.me/theorems/7d735916-3447-46b3-9c1a-a3750861d86e
-- title:
--   YukonModule.VCVio.CryptoFoundations.IdenSchemeWithAbort.part0
-- statement:
--   Source module VCVio.CryptoFoundations.IdenSchemeWithAbort.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/IdenSchemeWithAbort.lean
--
--   yukon-proof-operation:9985103443aa18226807818295353d8a31b9ad80d026e1aa3779acffb22ad522
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OTk4NTEwMzQ0M2FhMTgyMjY4MDc4MTgyOTUzNTNkOGEzMWI5YWQ4MGQwMjZlMWFhMzc3OWFjZmZiMjJhZDUyMiIsImhhc2giOiI2YjVjOWU4OWM5YTc5ZWYyMjExNTIwYmJhZWZiODM4NjcyOTFjZWYxNDQxZDk3YzQ2NDBhNjZmOTA1YmViYWU3Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9mNmZmYWRhNjIxMDc2ODYxNTI2YjYyM2MiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_97cb7c7d84a051f4f06c406f

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
meta import Definitions.Def_Yukon_97cb7c7d84a051f4f06c406f
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
set_option backward.isDefEq.respectTransparency.types false
/-!
# Identification Scheme with Aborts

This file defines a structure for identification schemes with aborts, as used in ML-DSA
(CRYSTALS-Dilithium). Unlike a standard Σ-protocol (`SigmaProtocol`), the prover's response
may fail (abort), in which case the protocol is retried. This abort mechanism is essential for
the security of lattice-based schemes where masking must hide the secret.

The structure follows the EasyCrypt formalization in `IDSabort.ec` (formosa-crypto/dilithium).

## Type Parameters

- `Stmt`: statement (public key)
- `Wit`: witness (secret key)
- `Commit`: public commitment (sent to the verifier)
- `PrvState`: private prover state (retained between commit and respond)
- `Chal`: verifier challenge
- `Resp`: prover response
- `rel`: the relation proven by the protocol

## Main Definitions

- `IdenSchemeWithAbort`: identification scheme where `respond` returns `Option Resp`
- `IdenSchemeWithAbort.Complete`: honest prover convinces verifier (conditioned on non-abort)
- `IdenSchemeWithAbort.HVZK`: transcript distribution is within a stated TV-distance
  of a simulator
- `IdenSchemeWithAbort.PerfectHVZK`: exact transcript distribution matching with a simulator
- `IdenSchemeWithAbort.CommitmentRecoverable`: ability to recover commitment from the transcript

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
- EasyCrypt `IDSabort.ec`
-/

@[expose] public section

open OracleSpec OracleComp

/-- An identification scheme with aborts for statements in `Stmt` and witnesses in `Wit`, where
`rel : Stmt → Wit → Bool` is the proven relation. The prover's commitment is split into a public
part `Commit` (sent to the verifier) and a private state `PrvState`. The verifier's challenge is
in `Chal`, and the prover's response (which may abort) is in `Resp`.

Unlike `SigmaProtocol`, the `respond` function returns `Option Resp` — `none` indicates an abort
and the protocol must be retried. This is the key mechanism used in Dilithium/ML-DSA to ensure
that the response distribution is independent of the secret. -/
structure IdenSchemeWithAbort
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  /-- Generate a commitment: returns a public commitment and private prover state. -/
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  /-- Respond to a challenge. Returns `none` if the response would leak information about
  the secret (abort), in which case the protocol is retried from scratch. -/
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) :
    ProbComp (Option Resp)
  /-- Deterministic verification: check that the response is valid for the given
  statement, commitment, and challenge. -/
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool

namespace IdenSchemeWithAbort

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

section HonestExecution

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- A single honest execution producing an optional transcript `(Commit, Chal, Resp)`.
Returns `none` if the prover aborts. -/
def honestExecution (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (s : Stmt) (w : Wit) :
    ProbComp (Option (Commit × Chal × Resp)) := do
  let (cm, st) ← ids.commit s w
  let c ← $ᵗ Chal
  let oz ← ids.respond s w st c
  return oz.map fun z => (cm, c, z)

end HonestExecution

section Completeness

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- An identification scheme with aborts is complete if: whenever the prover does not abort,
the verifier always accepts. -/
def Complete (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel) : Prop :=
  ∀ s w, rel s w = true →
    Pr[= true | do
      let t? ← ids.honestExecution s w
      return match t? with
        | some (cm, c, z) => ids.verify s cm c z
        | none => true
    ] = 1

/-- Support-level consequence of completeness: any non-aborting honest transcript in the
support has an accepting verification. -/
lemma verify_of_complete (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (hc : ids.Complete) {s : Stmt} {w : Wit} (hrel : rel s w = true)
    {cm : Commit} {c : Chal} {z : Resp}
    (h_mem : some (cm, c, z) ∈ support (ids.honestExecution s w)) :
    ids.verify s cm c z = true :=
  ((probOutput_eq_one_iff_forall _ _).1 (hc s w hrel)).2 _
    ((mem_support_bind_iff _ _ _).2 ⟨_, h_mem, by simp⟩)

end Completeness

section HVZK

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- Approximate honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover is within total variation
distance `ζ_zk` of the distribution produced by the simulator.

Both distributions are over `Option (Commit × Chal × Resp)`, where `none` represents an abort.
The parameter `ζ_zk` captures both transcript mismatch and abort-probability mismatch. -/
def HVZK (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) (ζ_zk : ℝ) : Prop :=
  ∀ s w, rel s w = true →
    tvDist (ids.honestExecution s w) (sim s) ≤ ζ_zk

/-- Exact honest-verifier zero-knowledge for an identification scheme with aborts:
the transcript distribution produced by the honest prover exactly matches the
distribution produced by the simulator. -/
def PerfectHVZK (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) : Prop :=
  ∀ s w, rel s w = true →
    𝒟[ids.honestExecution s w] = 𝒟[sim s]

/-- The perfect HVZK property is equivalent to the approximate HVZK property with `ζ_zk = 0`. -/
@[grind =]
lemma perfectHVZK_iff_hvzk_zero
    (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp))) :
    ids.PerfectHVZK sim ↔ ids.HVZK sim 0 := by
  simp [PerfectHVZK, HVZK, ← tvDist_eq_zero_iff, le_antisymm_iff, tvDist_nonneg]

end HVZK

section CommitmentRecoverability

/-- Commitment recoverability: any accepting transcript determines the public commitment
from the statement, challenge, and response alone. This property is required for the
CMA-to-NMA reduction in the Fiat-Shamir with aborts security proof.

In Dilithium/ML-DSA, the commitment `w1` can be recomputed as `highBits(Az - c*t)`. -/
def CommitmentRecoverable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (recover : Stmt → Chal → Resp → Commit) : Prop :=
  ∀ s cm c z,
    ids.verify s cm c z = true →
    recover s c z = cm

end CommitmentRecoverability

section Impersonation

/-- An adversary for the impersonation game against an identification scheme with aborts.
The adversary sees the public key (statement), produces a commitment together with an
internal state, and then responds to a challenge using that state. -/
structure ImpAdv (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
    (AdvSt : Type) where
  commit (s : Stmt) : ProbComp (Commit × AdvSt)
  respond (s : Stmt) (c : Chal) (st : AdvSt) : ProbComp Resp

variable [SampleableType Chal] [IsUniformSpec unifSpec]

/-- The impersonation experiment: the adversary tries to produce a valid transcript
without knowing the witness, against a fixed statement `s`. -/
def impExp {ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel}
    {AdvSt : Type} (adv : ImpAdv ids AdvSt) (s : Stmt) : ProbComp Bool := do
  let (cm, st) ← adv.commit s
  let c ← $ᵗ Chal
  let z ← adv.respond s c st
  return ids.verify s cm c z

end Impersonation

end IdenSchemeWithAbort


