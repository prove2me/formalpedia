-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
-- name    : Submission_ThreeSum_TernaryCoverTrimming
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:44:25.809033+00:00
-- url     : https://prove2.me/theorems/d7876119-bc9b-40c8-8b7d-fe7482e383ff
-- title:
--   Ternary Cover Trimming
-- statement:
--   Definitions and structural lemmas for Ternary Cover Trimming, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTrimming.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option autoImplicit false
namespace ThreeSum.TernaryCoverTrimming
open Finset TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]
abbrev Word := ι → K
abbrev Weight := Coordinate ι → K
def bucketSize (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (w : Weight (ι := ι) (K := K))
    (a : K) : ℕ :=
  (vertices.filter fun u => linearHash (vector u) w = a).card
def loadedMass (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) : ℕ :=
  ∑ w ∈ event, bucketSize vertices vector w a
def heavyEvent (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) (B : ℕ) :
    Finset (Weight (ι := ι) (K := K)) :=
  event.filter fun w => B < bucketSize vertices vector w a
def trimmedPairEvent (x y : Word (ι := ι) (K := K)) (a b : K)
    (VL VR : Finset (Word (ι := ι) (K := K))) (B : ℕ) : Finset (Weight (ι := ι) (K := K)) :=
  (pairEvent x y a b).filter fun w =>
    bucketSize VL leftVector w a ≤ B ∧ bucketSize VR rightVector w b ≤ B
end ThreeSum.TernaryCoverTrimming


