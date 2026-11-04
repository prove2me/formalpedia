-- Prove2me | Definitions.Def_Submission_Weighted_Addresses
-- name    : Submission_Weighted_Addresses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:25:22.475208+00:00
-- url     : https://prove2.me/theorems/fd967583-a9ca-4c41-af23-bbbdb3b38951
-- title:
--   Addresses
-- statement:
--   Definitions and structural lemmas for Addresses, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Addresses.lean

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
set_option autoImplicit false
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


