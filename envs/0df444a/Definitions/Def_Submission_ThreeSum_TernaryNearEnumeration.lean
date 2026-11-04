-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
-- name    : Submission_ThreeSum_TernaryNearEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:31:43.250525+00:00
-- url     : https://prove2.me/theorems/1444899c-b899-4393-b738-67aeaef066cc
-- title:
--   Ternary Near Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Near Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
namespace ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
def digits (q D : ℕ) : List ℕ :=
  (List.range (q+1)).filter (fun r => q-r ≤ D)
def words : List ℕ → ℕ → List (List ℕ)
  | [], _ => [[]]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (words qs (D-(q-r))).map (List.cons r)
def visits : List ℕ → ℕ → ℕ
  | [], _ => 1
  | q :: qs, D => 1+((digits q D).map fun r => visits qs (D-(q-r))).sum
def Admitted : List ℕ → List ℕ → ℕ → Prop
  | [], [], _ => True
  | q :: qs, r :: rs, D => r ≤ q ∧ q-r ≤ D ∧ Admitted qs rs (D-(q-r))
  | _, _, _ => False
def codes : List ℕ → ℕ → List ℕ
  | [], _ => [0]
  | q :: qs, D => (digits q D).flatMap fun r =>
      (codes qs (D-(q-r))).map (fun a => digitCode r*4^qs.length+a)
end ThreeSum.TernaryNearEnumeration


