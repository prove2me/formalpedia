-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:25:22.725803+00:00
-- url     : https://prove2.me/theorems/3f155c2c-0798-4b42-8213-8275e29f8c74
-- title:
--   TernaryOversizePrime
-- statement:
--   Definitions and structural lemmas for TernaryOversizePrime, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryOversizePrime.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
namespace ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
def rootCandidates (K M : ℕ) : Finset ℕ :=
  (range (M+1)).filter fun s => M ≤ s^K
def rootCeiling (K M : ℕ) : ℕ :=
  if h : (rootCandidates K M).Nonempty then (rootCandidates K M).min' h else 1
def inflation (K m : ℕ) : ℕ := rootCeiling K (outputSize m)
def inflatedThreshold (K m : ℕ) : ℕ := threshold m*(inflation K m)^2
opaque nativePrimeData (K m : ℕ) : {p : ℕ // p.Prime ∧
    p=LocalCoverBounds.selectedPrime (inflatedThreshold K m)} :=
  ⟨LocalCoverBounds.selectedPrime (inflatedThreshold K m),
    (LocalCoverBounds.selectedPrime_spec (inflatedThreshold K m)).1,rfl⟩
def nativePrime (K m : ℕ) : ℕ := (nativePrimeData K m).val
theorem nativePrime_prime (K m : ℕ) : (nativePrime K m).Prime :=
  (nativePrimeData K m).property.1
instance (priority := 2000) (K m : ℕ) : Fact (nativePrime K m).Prime := ⟨nativePrime_prime K m⟩
def inflatedFrequency (K m : ℕ) : ℕ := frequencyFactor m*(inflation K m)^4
attribute [irreducible] nativePrime
instance (priority := 3000) (K m : ℕ) : NeZero (nativePrime K m) :=
  ⟨(nativePrime_prime K m).ne_zero⟩
def nativeCatalog (K m : ℕ) : List (WeightedGlobalCoverGoodMaps.Weight m (nativePrime K m)) := univ.toList
def nativeFamily (K m k : ℕ) := Cover.greedyChoices (nativeCatalog K m)
  (Covers m (nativePrime K m) (sourceCap m (nativePrime K m))
    (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)) univ
  (inflatedFrequency K m*(Nat.log2 (nativePrime K m^2)+1))
end ThreeSum.WeightedGlobalOversizePrime
end
end WeightedCache3SUMRefinement_e1ae71d


