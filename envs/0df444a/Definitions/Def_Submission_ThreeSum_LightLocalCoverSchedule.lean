-- Prove2me | Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
-- name    : Submission_ThreeSum_LightLocalCoverSchedule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:43:44.393495+00:00
-- url     : https://prove2.me/theorems/c3eb87b3-bc64-4fd8-940c-fc0e6493d92d
-- title:
--   Light Local Cover Schedule
-- statement:
--   Definitions and structural lemmas for Light Local Cover Schedule, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverSchedule.lean

import Definitions.Def_Submission_ThreeSum_LightLocalCoverTransport
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
set_option autoImplicit false
namespace ThreeSum.LightLocalCoverSchedule
open Finset LocalHashMoments LocalCoverBounds GlobalEncoding
def rows (h : ℕ) : ℕ := (localPrime h)^(2*(512*h))
def cols (h : ℕ) : ℕ := localPrime h*localPrime h
def candidate (h i : ℕ) : Weight (512*h) (LocalField h) :=
  WeightEnumeration.decodedWeight (512*h) (localPrime h) i
def target (h r : ℕ) : LocalField h × LocalField h :=
  (((r/localPrime h : ℕ) : LocalField h),((r%localPrime h : ℕ) : LocalField h))
def matrix (h i r : ℕ) : ℕ :=
  LocalCoverMatrix.entry (candidate h i) h (localBucketCap h) r
def indices (h : ℕ) : List ℕ :=
  BooleanGreedy.choices (matrix h) (rows h) (cols h) (scheduleSize h)
def candidateAt (h : ℕ) (s : Occurrence h) : ℕ := (indices h).getD s.val 0
end ThreeSum.LightLocalCoverSchedule


