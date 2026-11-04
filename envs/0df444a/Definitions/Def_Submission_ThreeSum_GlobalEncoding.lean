-- Prove2me | Definitions.Def_Submission_ThreeSum_GlobalEncoding
-- name    : Submission_ThreeSum_GlobalEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:08:18.44939+00:00
-- url     : https://prove2.me/theorems/a7c9c456-4bbd-4f10-8d17-efd5c1e9d921
-- title:
--   Global Encoding
-- statement:
--   Definitions and structural lemmas for Global Encoding, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalGraph_output_card
import Theorems.Thm_ThreeSum_LocalHashMoments_localSchedule_length
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
def scheduleSize (h : ℕ) : ℕ := scheduleLength h (localPrime h)
theorem scheduleSize_eq_length (h : ℕ) : scheduleSize h = (localSchedule h).length := by
  rw [localSchedule_length]
  rfl
abbrev Occurrence (h : ℕ) := Fin (scheduleSize h)
def mapAt (h : ℕ) (i : Occurrence h) : Weight (512 * h) (LocalField h) :=
  (localSchedule h).get (Fin.cast (scheduleSize_eq_length h) i)
def Survives (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) : Prop :=
  HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (left e)) ≤ localBucketCap h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (right e)) ≤ localBucketCap h
instance (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) :
    Decidable (Survives h i e) := by unfold Survives; infer_instance
abbrev RetainedChoice (h : ℕ) :=
  {p : Occurrence h × Edge (512 * h) h // Survives h p.1 p.2}
def occurrence {h : ℕ} (c : RetainedChoice h) : Occurrence h := c.val.1
def edge {h : ℕ} (c : RetainedChoice h) : Edge (512 * h) h := c.val.2
def rawHash {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) : ℤ :=
  ∑ i, ((w (i, s i)).val : ℤ)
def rawLeft {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (left (edge c))
def rawRight {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (right (edge c))
def representations (h J : ℕ) (a b : ℤ) : Finset (List (RetainedChoice h)) :=
  Radix.representations (localPrime h) rawLeft rawRight J a b
def globalModulus (h J : ℕ) : ℤ := (localPrime h : ℤ) ^ J
def representationCap (h J : ℕ) : ℕ :=
  (scheduleSize h * localBucketCap h ^ 2) ^ J
theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (RetainedChoice h)) :
    xs ∈ representations h J a b ↔ xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs := by
  exact Radix.mem_representations (localPrime h)
    (by exact_mod_cast (localPrime_pos h).ne') rawLeft rawRight J a b xs
def rawOutput {h L : ℕ} (w : Weight L (LocalField h)) (Q : Finset (Fin L)) : ℤ :=
  ∑ i, if i ∈ Q then 0 else ((w (i, true)).val : ℤ) - ((w (i, false)).val : ℤ)
abbrev OutputBlock (h : ℕ) :=
  Occurrence h × {Q // Q ∈ LayerCounts.vertices (512 * h) (2 * h)}
def blockOfChoice {h : ℕ} (c : RetainedChoice h) : OutputBlock h :=
  (occurrence c, ⟨output (edge c), LayerCounts.mem_vertices.mpr (output_card (edge c))⟩)
def blockKey {h : ℕ} (b : OutputBlock h) : ℤ := rawOutput (mapAt h b.1) b.2.val
abbrev GlobalOutput (h J : ℕ) := Fin J → OutputBlock h
def globalKey {h J : ℕ} (q : GlobalOutput h J) : ℤ :=
  Radix.positionalHash (localPrime h) blockKey (List.ofFn q)
def outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    GlobalOutput h J :=
  fun i => blockOfChoice (xs.get (Fin.cast hlen.symm i))
end ThreeSum.GlobalEncoding


