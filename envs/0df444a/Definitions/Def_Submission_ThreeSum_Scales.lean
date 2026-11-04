-- Prove2me | Definitions.Def_Submission_ThreeSum_Scales
-- name    : Submission_ThreeSum_Scales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:38.293623+00:00
-- url     : https://prove2.me/theorems/96367ad3-36cd-4270-bdb6-985097d6bde1
-- title:
--   Scales
-- statement:
--   Definitions and structural lemmas for Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
set_option autoImplicit false
namespace ThreeSum.Scales
open Filter Real
open scoped Topology
def inputBits (n : ℕ) : ℕ := Nat.log2 n
def microSize (m : ℕ) : ℕ := 2 * (Nat.nthRoot 3 m / 2)
def blockCount (m : ℕ) : ℕ := 20 * (m / (100 * microSize m))
def totalSize (m : ℕ) : ℕ := blockCount m * microSize m
def muZero (n : ℕ) : ℕ := microSize (inputBits n)
def mu (n : ℕ) : ℕ := totalSize (inputBits n)
def typedOutputs (n : ℕ) : ℕ :=
  ((256 * muZero n).choose (muZero n)) ^ blockCount (inputBits n)
def localSearch (C n : ℕ) : ℕ := 2 ^ (C * muZero n ^ 2)
def scheduleFactor (C n : ℕ) : ℕ :=
  (256 * muZero n + 1) ^ (C * blockCount (inputBits n))
def windowExponent (m : ℕ) : ℕ := Nat.sqrt m + 1
def primeWindow (n : ℕ) : ℕ := 2 ^ windowExponent (inputBits n)
def primeDepth (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.log (4 * primeWindow n) (R n / 4)
def primeLoss (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  32 * primeWindow n * 4 ^ primeDepth R n
def microHalf (m : ℕ) : ℕ := Nat.nthRoot 3 m / 2
def localRadix (n : ℕ) : ℕ := LocalCoverBounds.localPrime (microHalf (inputBits n))
def radix (n : ℕ) : ℕ := localRadix n ^ blockCount (inputBits n)
def divisorBudget (k n : ℕ) : ℕ := Nat.log (primeWindow n) (3 * n ^ k)
def scoreLoss (k n : ℕ) : ℕ :=
  (16 * (k + 2) * (inputBits n + 1)) ^ primeDepth radix n
def candidateCount (n : ℕ) : ℕ := (PrimeDensity.candidates (primeWindow n)).card
noncomputable section
end
end ThreeSum.Scales


