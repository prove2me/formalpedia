-- Prove2me | Definitions.Def_Submission_ThreeSum_BandPrimeScales
-- name    : Submission_ThreeSum_BandPrimeScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:41:48.53795+00:00
-- url     : https://prove2.me/theorems/5af04946-324e-4507-b450-0faee3060d33
-- title:
--   Band Prime Scales
-- statement:
--   Definitions and structural lemmas for Band Prime Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandPrimeScales.lean

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
set_option autoImplicit false
namespace ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
def modulus (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  LightBandPrimeConstruction.modulus (primeWindow n) nA nB nC (bandSize n)
    A B C rs (primeDepth radix n)
def score (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  BandWeightedScore.score (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) q nA nB nC (bandSize n) A B C rs
def physicalMass (n q nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.allProducts nA nB nC (bandSize n) rs)
    (ModuloCounts.difference (BandRawA.valueAt nA (bandSize n) rs A) B C)
    (Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
      (LightPrimePool.size (primeWindow n)))) q
end ThreeSum.BandPrimeScales


