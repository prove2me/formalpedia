-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalHashMoments
-- name    : Submission_ThreeSum_LocalHashMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:20:21.360202+00:00
-- url     : https://prove2.me/theorems/2d78867e-34fa-4a40-8c1b-09f919d81d6f
-- title:
--   Local Hash Moments
-- statement:
--   Definitions and structural lemmas for Local Hash Moments, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalHashMoments.lean

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_prime
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.LocalHashMoments
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}
abbrev Weight (L : ℕ) (K : Type*) := Fin L × Bool → K
def bucketBound (L h p : ℕ) : ℕ := bucketCap (vertexCount L h) p
def hitCount (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : ℕ :=
  HashFamily.incidenceCount (fun e : Edge L h =>
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B) w
def Covers (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : Prop :=
  hitCount L h B w target ≠ 0
instance instDecidableCovers (L h B : ℕ) :
    DecidableRel (Covers (K := K) L h B) := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))
instance weightInhabited : Inhabited (Weight L K) := ⟨fun _ => 0⟩
def coordinates (L : ℕ) : List (Fin L × Bool) :=
  (List.finRange L).flatMap (fun i => [(i, false), (i, true)])
theorem mem_coordinates (i : Fin L × Bool) : i ∈ coordinates L := by
  obtain ⟨i, b⟩ := i
  cases b <;> simp [coordinates]
def allWeights (L : ℕ) (values : List K) : List (Weight L K) :=
  (List.pi (coordinates L) (fun _ => values)).map
    (fun f i => f i (mem_coordinates i))
def scheduleLength (h p : ℕ) : ℕ :=
  320 * (2 * h + 1) * (Nat.log2 (p ^ 2) + 1)
def schedule (L h : ℕ) (values : List K) :
    List (Weight L K) :=
  Cover.greedyChoices (allWeights L values)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (scheduleLength h (Fintype.card K))
instance localPrimeFact (h : ℕ) : Fact (Nat.Prime (localPrime h)) :=
  ⟨localPrime_prime h⟩
abbrev LocalField (h : ℕ) := ZMod (localPrime h)
def localValues (h : ℕ) : List (LocalField h) :=
  (List.range (localPrime h)).map (fun x : ℕ => (x : LocalField h))
def localSchedule (h : ℕ) : List (Weight (512 * h) (LocalField h)) :=
  schedule (512 * h) h (localValues h)
end ThreeSum.LocalHashMoments


