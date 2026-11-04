-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryAddresses
-- name    : Submission_ThreeSum_TernaryAddresses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:24:21.205254+00:00
-- url     : https://prove2.me/theorems/54dd61b1-6ffa-4719-92c5-116e82889e72
-- title:
--   Ternary Addresses
-- statement:
--   Definitions and structural lemmas for Ternary Addresses, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
set_option autoImplicit false
namespace ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
def digitCode (d : ℕ) : ℕ := if d = 2 then 3 else d
def code : List ℕ → ℕ
  | [] => 0
  | d :: xs => digitCode d * 4 ^ xs.length + code xs
def codes : ℕ → ℕ → List ℕ
  | 0, _ => [0]
  | n + 1, t => (digits t).flatMap fun d =>
      (codes n (t - d)).map (fun a => digitCode d * 4 ^ n + a)
end ThreeSum.TernaryAddresses


