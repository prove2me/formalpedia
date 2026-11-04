-- Prove2me | Definitions.Def_Submission_ThreeSum_SubsetAddress
-- name    : Submission_ThreeSum_SubsetAddress
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:23:58.58214+00:00
-- url     : https://prove2.me/theorems/1ce08f13-2db0-4ccf-a92c-d328df11ecd5
-- title:
--   Subset Address
-- statement:
--   Definitions and structural lemmas for Subset Address, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetAddress.lean

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Combinatorics.Colex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace ThreeSum.SubsetAddress
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
def weight : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, m => if m < 2 ^ L then weight L m else weight L (m - 2 ^ L) + 1
def IsMask (L k m : ℕ) : Prop := m < 2 ^ L ∧ weight L m = k
instance (L k m : ℕ) : Decidable (IsMask L k m) := by
  unfold IsMask
  infer_instance
def layerRank : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L + 1, k, m =>
      if m < 2 ^ L then layerRank L k m
      else L.choose k + layerRank L (k - 1) (m - 2 ^ L)
def enumerateLayer : ℕ → ℕ → List ℕ
  | _, 0 => [0]
  | 0, _ + 1 => []
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        enumerateLayer L (k + 1) ++ (enumerateLayer L k).map (fun m => 2 ^ L + m)
      else []
def enumerationWork : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | L + 1, k + 1 =>
      if k + 1 ≤ L + 1 then
        1 + enumerationWork L (k + 1) + enumerationWork L k +
          (enumerateLayer L (k + 1)).length + (enumerateLayer L k).length
      else 1
def layerOffset (L k : ℕ) : ℕ := ∑ r ∈ Finset.range k, L.choose r
def downsetCap (L cut : ℕ) : ℕ := layerOffset L (min cut L + 1)
def downsetRank (L m : ℕ) : ℕ :=
  layerOffset L (weight L m) + layerRank L (weight L m) m
def enumerateThrough (L : ℕ) : ℕ → List ℕ
  | 0 => enumerateLayer L 0
  | k + 1 => enumerateThrough L k ++ enumerateLayer L (k + 1)
def enumerateDownset (L cut : ℕ) : List ℕ := enumerateThrough L (min cut L)
def throughWork (L : ℕ) : ℕ → ℕ
  | 0 => enumerationWork L 0
  | k + 1 => throughWork L k + enumerationWork L (k + 1) +
      1 + (enumerateThrough L k).length
def downsetEnumerationWork (L cut : ℕ) : ℕ := throughWork L (min cut L)
def maskOf (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i
def natPositions {L : ℕ} (s : Finset (Fin L)) : Finset ℕ := s.map Fin.valEmbedding
def subsetMask {L : ℕ} (s : Finset (Fin L)) : ℕ := maskOf (natPositions s)
def subsetRank {L : ℕ} (s : Finset (Fin L)) : ℕ := downsetRank L (subsetMask s)
def recordAddress {L : ℕ} (flags : Finset (Fin L)) (freeCount : ℕ) : ℕ :=
  subsetRank flags * (L + 1) + freeCount
end ThreeSum.SubsetAddress


