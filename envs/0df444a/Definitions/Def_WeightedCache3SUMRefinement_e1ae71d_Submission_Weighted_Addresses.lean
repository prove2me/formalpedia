-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:05:46.743133+00:00
-- url     : https://prove2.me/theorems/3fd86725-c1fc-4118-a3c3-00bffae6529c
-- title:
--   Addresses
-- statement:
--   Definitions and structural lemmas for Addresses, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Addresses.lean

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
def digitCode (d : ℕ) : ℕ := if d = 2 then 3 else d
def code : List ℕ → ℕ
  | [] => 0
  | d :: xs => digitCode d * 4 ^ xs.length + code xs
def codes : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | n + 1, t => (digits t).flatMap fun d =>
      (codes n (t - digitCost d)).map (fun a => digitCode d * 4 ^ n + a)
end ThreeSum.WeightedAddresses
end WeightedCache3SUMRefinement_e1ae71d


