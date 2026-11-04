-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
-- name    : Submission_Weighted_Global_TernaryCoverScale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:27.257206+00:00
-- url     : https://prove2.me/theorems/02451a73-6710-48af-b60e-244b01ae6649
-- title:
--   Ternary Cover Scale
-- statement:
--   Definitions and structural lemmas for Ternary Cover Scale, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec

set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
def threshold (m : ℕ) : ℕ :=
  (vertices (fixedLength m) (fixedPi m)).card * (2^(fixedPi m 1)*3^(fixedPi m 2))
def prime (m : ℕ) : ℕ := LocalCoverBounds.selectedPrime (threshold m)
theorem prime_prime (m : ℕ) : (prime m).Prime :=
  (LocalCoverBounds.selectedPrime_spec (threshold m)).1
instance (m : ℕ) : Fact (prime m).Prime := ⟨prime_prime m⟩
def catalog (m : ℕ) : List (WeightedGlobalCoverGoodMaps.Weight m (prime m)) :=
  Finset.univ.toList
def family (m k : ℕ) := Cover.greedyChoices (catalog m)
  (WeightedGlobalCoverFrequency.Covers m (prime m) (sourceCap m (prime m))
    (rawThreshold (prime m) (sourceCap m (prime m)) k)) Finset.univ
  (frequencyFactor m*(Nat.log2 (prime m^2)+1))
def momentOrder (C : ℕ) : ℕ := 100000*C
def scaleAux (C c d : ℕ) : ℕ :=
  C*momentOrder C*(46*d+367+(2*d+15)+1)+
    C*(8*(momentOrder C)^2+momentOrder C+26)+c+2
def scale (C c d : ℕ) : ℕ := 2^(2*scaleAux C c d)
def localFactor (C c d : ℕ) : ℕ :=
  (c*(fixedLength (scale C c d)+1)^d)*
    (family (scale C c d) (momentOrder C)).length*
    rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
      (momentOrder C)
def outputSize (m : ℕ) : ℕ := (vertices (fixedLength m) (fixedPi m)).card
def radixLength (m n : ℕ) : ℕ := Nat.clog (outputSize m) (n^2)
end ThreeSum.WeightedGlobalCoverScale


