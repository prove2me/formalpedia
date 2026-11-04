-- Prove2me | Definitions.Def_Submission_ThreeSum_BandEnumeration
-- name    : Submission_ThreeSum_BandEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:52:28.386579+00:00
-- url     : https://prove2.me/theorems/64967ee5-5e30-4fd9-a829-2aec381b3343
-- title:
--   Band Enumeration
-- statement:
--   Definitions and structural lemmas for Band Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandEnumeration.lean

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
set_option autoImplicit false
namespace ThreeSum.BandEnumeration
structure Family where
  size : ℕ
  lower : ℕ → ℤ
  upper : ℕ → ℤ
  nonempty : ∀ i < size, lower i ≤ upper i
  sorted : ∀ i j, i ≤ j → j < size → lower i ≤ lower j
  separated : ∀ i j, i < j → j < size → upper i < lower j
namespace Family
abbrev Index (A : Family) := Fin A.size
def lo (A : Family) (i : A.Index) : ℤ := A.lower i
def hi (A : Family) (i : A.Index) : ℤ := A.upper i
def lookup (A : Family) (x : ℤ) : Option A.Index := do
  let i ← BinarySearch.locate A.lower A.upper A.size x
  if h : i < A.size then some ⟨i, h⟩ else none
end Family
open Family
abbrev Triple (A B C : Family) := A.Index × (B.Index × C.Index)
abbrev Owner (A B C : Family) := (B.Index × C.Index) ⊕ (A.Index × (B.Index ⊕ C.Index))
def relevant (A B C : Family) (t : Triple A B C) : Prop :=
  Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t
instance (A B C : Family) (t : Triple A B C) : Decidable (relevant A B C t) :=
  inferInstanceAs (Decidable (Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t))
def owner (A B C : Family) (t : Triple A B C) : Owner A B C :=
  Bands.tripleOwner A.lo B.lo B.hi C.lo t
def candidate (A B C : Family) : Owner A B C → Option (Triple A B C)
  | .inl (j, k) => (A.lookup (C.lo k - B.hi j)).map fun i => (i, j, k)
  | .inr (i, .inl j) => (C.lookup (A.lo i + B.lo j)).map fun k => (i, j, k)
  | .inr (i, .inr k) => (B.lookup (C.lo k - A.lo i)).map fun j => (i, j, k)
def checkedCandidate (A B C : Family) (o : Owner A B C) : Option (Triple A B C) := do
  let t ← candidate A B C o
  if relevant A B C t ∧ owner A B C t = o then some t else none
def owners (A B C : Family) : List (Owner A B C) :=
  (List.finRange B.size ×ˢ List.finRange C.size).map
    (fun p => (Sum.inl p : Owner A B C)) ++
  (List.finRange A.size ×ˢ
    ((List.finRange B.size).map (fun j => (Sum.inl j : B.Index ⊕ C.Index)) ++
      (List.finRange C.size).map Sum.inr)).map (fun p => (Sum.inr p : Owner A B C))
def enumerate (A B C : Family) : List (Triple A B C) :=
  (owners A B C).filterMap (checkedCandidate A B C)
def lookupComparisons (A B C : Family) : Owner A B C → ℕ
  | .inl (j, k) => BinarySearch.comparisons A.lower (C.lo k - B.hi j)
      (Nat.log 2 A.size + 1) 0 A.size
  | .inr (i, .inl j) => BinarySearch.comparisons C.lower (A.lo i + B.lo j)
      (Nat.log 2 C.size + 1) 0 C.size
  | .inr (i, .inr k) => BinarySearch.comparisons B.lower (C.lo k - A.lo i)
      (Nat.log 2 B.size + 1) 0 B.size
end ThreeSum.BandEnumeration


