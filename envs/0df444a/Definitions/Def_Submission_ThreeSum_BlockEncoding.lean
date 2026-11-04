-- Prove2me | Definitions.Def_Submission_ThreeSum_BlockEncoding
-- name    : Submission_ThreeSum_BlockEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:22:29.623698+00:00
-- url     : https://prove2.me/theorems/6f412ae3-064b-4ac7-9c9d-16fb6d90fcac
-- title:
--   Block Encoding
-- statement:
--   Definitions and structural lemmas for Block Encoding, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Theorems.Thm_ThreeSum_BlockRows_mem_row
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
attribute [local simp] ThreeSum.BlockRows.mem_row
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet


set_option autoImplicit false
namespace ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
abbrev Occurrences (h J : ℕ) := Fin J → Occurrence h
def outputOccurrences {h J : ℕ} (q : GlobalOutput h J) : Occurrences h J := fun i => (q i).1
def leftSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.1
def rightSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.2
def outputSubset {h J : ℕ} (q : GlobalOutput h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (q i).2.val
def LeftAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (leftWord (row S i))) ≤ localBucketCap h
def RightAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (rightWord (row S i))) ≤ localBucketCap h
instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (LeftAllowed o S) := by unfold LeftAllowed; infer_instance
instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (RightAllowed o S) := by unfold RightAllowed; infer_instance
def endpointLeft {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (leftWord (row S i)))
def endpointRight {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (rightWord (row S i)))
def fromSubsets {h J : ℕ} (o : Occurrences h J) (S V : Finset (Coord J (512 * h)))
    (hS : LeftAllowed o S) (hV : RightAllowed o V) (hd : Disjoint S V) : ChoiceTuple h J :=
  fun i => ⟨(o i, ⟨(row S i, row V i), LayerCounts.mem_edgeSet.mpr
    ⟨(hS i).1, (hV i).1, Finset.disjoint_left.mpr (fun _ hx hy =>
      Finset.disjoint_left.mp hd (mem_row.mp hx) (mem_row.mp hy))⟩⟩),
    ⟨(hS i).2, (hV i).2⟩⟩
section Histograms
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
def leftWeights {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ)
    (S : Finset (Coord J (512 * h))) : ℕ :=
  if LeftAllowed o S then
    ∑ j ∈ B, if globalModulus h J ∣ b j % P - endpointLeft o S then 1 else 0
  else 0
def rightWeights {h J : ℕ} (o : Occurrences h J) (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (V : Finset (Coord J (512 * h))) : ℕ :=
  if RightAllowed o V then
    ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - endpointRight o V then 1 else 0
  else 0
end Histograms
end ThreeSum.BlockEncoding


