-- Prove2me | Definitions.Def_Yukon_b2c54449f2b5ff5eadbe0d35
-- name    : Yukon_b2c54449f2b5ff5eadbe0d35
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:59.640992+00:00
-- url     : https://prove2.me/theorems/86b49da3-463e-46b7-b52b-ec40cc9e9ff9
-- title:
--   YukonModule.VCVio.CryptoFoundations.AsymmEncAlg.Defs.part0
-- statement:
--   Source module VCVio.CryptoFoundations.AsymmEncAlg.Defs.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/AsymmEncAlg/Defs.lean
--
--   yukon-proof-operation:b8e258b937e8abab08a2b466a31d59cdecdb7df5a4417794f8b7c009e7f4c059
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YjhlMjU4YjkzN2U4YWJhYjA4YTJiNDY2YTMxZDU5Y2RlY2RiN2RmNWE0NDE3Nzk0ZjhiN2MwMDllN2Y0YzA1OSIsImhhc2giOiIwZjM2NDgwNjRkMDE0YmVkNDBiMjE3OTAzM2IzZDA1MmExYmYyNTA0MzIyNDE3NTMyNjljZGM3ODcwMTdiMTZmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iMmM1NDQ0OWYyYjVmZjVlYWRiZTBkMzUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_44168058399b05f7fa2f05f3

public import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7

public import Definitions.Def_Yukon_55d30d3deeb7817ce41e3794

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
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.List.Sym
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
meta import Definitions.Def_Yukon_2a6b3412af2af8cd7980168b
meta import Definitions.Def_Yukon_44168058399b05f7fa2f05f3
meta import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
meta import Definitions.Def_Yukon_55d30d3deeb7817ce41e3794
set_option backward.isDefEq.respectTransparency.types false
/-!
# Asymmetric Encryption Schemes

Core definitions for asymmetric encryption schemes and correctness.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

universe u v w

/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`m` is the monad used to execute key generation, encryption, and decryption. The scheme data stays
purely algorithmic; probabilistic semantics and public-randomness injection are supplied
separately when defining security experiments. -/
@[ext]
structure AsymmEncAlg (m : Type → Type u) [Monad m] (M PK SK C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → m C
  decrypt : (sk : SK) → (c : C) → m (Option M)

/-- An explicit-coins asymmetric encryption scheme in the monad `m`.

Key generation runs in `m`, while encryption and decryption become pure once the randomness type
`R` is supplied explicitly. This is the natural refinement used by FO-style transforms, where the
coins are sampled externally or derived from an oracle. -/
structure AsymmEncAlg.ExplicitCoins (m : Type → Type u) [Monad m] (M PK SK R C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → (coins : R) → C
  decrypt : (sk : SK) → (c : C) → Option M

abbrev PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg
variable {m : Type → Type v} [Monad m] {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section map

variable {n : Type → Type w} [Monad n]

/-- Transport an asymmetric encryption scheme across a monad morphism by mapping each algorithmic
component. -/
def map (F : m →ᵐ n) : AsymmEncAlg n M PK SK C where
  keygen := F encAlg.keygen
  encrypt pk msg := F (encAlg.encrypt pk msg)
  decrypt sk c := F (encAlg.decrypt sk c)

@[simp]
lemma map_keygen {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) :
    (encAlg.map F).keygen = F encAlg.keygen := rfl

@[simp]
lemma map_encrypt {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) (pk : PK) (msg : M) :
    (encAlg.map F).encrypt pk msg = F (encAlg.encrypt pk msg) := rfl

@[simp]
lemma map_decrypt {encAlg : AsymmEncAlg m M PK SK C} (F : m →ᵐ n) (sk : SK) (c : C) :
    (encAlg.map F).decrypt sk c = F (encAlg.decrypt sk c) := rfl

end map

section Correct

variable [DecidableEq M]

/-- Correctness experiment: returns `true` iff decrypting the ciphertext recovers the message.

The game returns a `Bool` directly rather than using `guard`, so it does not require
`AlternativeMonad`. -/
def CorrectExp (msg : M) : m Bool := do
  let (pk, sk) ← encAlg.keygen
  let c ← encAlg.encrypt pk msg
  let msg' ← encAlg.decrypt sk c
  return decide (msg' = some msg)

/-- An asymmetric encryption scheme is perfectly correct under the given runtime when decrypting a
fresh encryption of any message succeeds with probability `1`. -/
def PerfectlyCorrect (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : M), Pr[= true | runtime.evalDist (encAlg.CorrectExp msg)] = 1

end Correct

namespace ExplicitCoins
variable {m : Type → Type v} [Monad m] {M PK SK R C : Type}
  (encAlg : AsymmEncAlg.ExplicitCoins m M PK SK R C)

/-- Forget the explicit-coins presentation by sampling the coins through the ambient runtime's
public-randomness capability. -/
def toAsymmEncAlg [SampleableType R] (runtime : ProbCompRuntime m) : AsymmEncAlg m M PK SK C :=
  { keygen := encAlg.keygen
    encrypt pk msg := do
      let r ← runtime.liftProbComp ($ᵗ R)
      return encAlg.encrypt pk msg r
    decrypt sk c := return encAlg.decrypt sk c }

end ExplicitCoins

end AsymmEncAlg


