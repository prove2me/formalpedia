-- Prove2me | Definitions.Def_Submission_Weighted_NearEnumeration
-- name    : Submission_Weighted_NearEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:31:42.692203+00:00
-- url     : https://prove2.me/theorems/24fe59f6-fd75-49b4-a484-f87a1c4ab36a
-- title:
--   Near Enumeration
-- statement:
--   Definitions and structural lemmas for Near Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean

import Definitions.Def_Submission_Weighted_Addresses
set_option autoImplicit false
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


