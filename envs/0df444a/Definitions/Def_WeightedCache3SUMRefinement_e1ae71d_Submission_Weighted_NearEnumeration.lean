-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:06:36.962865+00:00
-- url     : https://prove2.me/theorems/6813c252-cd7a-4dd0-af3b-bc9f54918efe
-- title:
--   NearEnumeration
-- statement:
--   Definitions and structural lemmas for NearEnumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearEnumeration.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
def digits (q D : ℕ) : List ℕ :=
  (List.range (q+1)).filter (fun r => digitCost q-digitCost r ≤ D)
def words : List ℕ → ℕ → List (List ℕ)
  | [], _ => [[]]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (words qs (D-(digitCost q-digitCost r))).map (List.cons r)
def visits : List ℕ → ℕ → ℕ
  | [], _ => 1
  | q :: qs, D => 1+((digits q D).map fun r => visits qs (D-(digitCost q-digitCost r))).sum
def Admitted : List ℕ → List ℕ → ℕ → Prop
  | [], [], _ => True
  | q :: qs, r :: rs, D => r ≤ q ∧ digitCost q-digitCost r ≤ D ∧ Admitted qs rs (D-(digitCost q-digitCost r))
  | _, _, _ => False
def codes : List ℕ → ℕ → List ℕ
  | [], _ => [0]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (codes qs (D-(digitCost q-digitCost r))).map (fun a => digitCode r*4^qs.length+a)
end ThreeSum.WeightedNearEnumeration
end WeightedCache3SUMRefinement_e1ae71d


