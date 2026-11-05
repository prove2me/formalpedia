-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:23:19.773348+00:00
-- url     : https://prove2.me/theorems/a448f0db-97b2-4c9c-9375-bb39672ae1bd
-- title:
--   TernaryCoverScale
-- statement:
--   Definitions and structural lemmas for TernaryCoverScale, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverScale.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_spec

set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
  C*momentOrder C*(56*d+437+(2*d+15)+1)+
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
end
end WeightedCache3SUMRefinement_e1ae71d


