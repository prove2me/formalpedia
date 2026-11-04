-- Prove2me | Definitions.Def_Submission_Weighted_NearBankEnumeration
-- name    : Submission_Weighted_NearBankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:35:48.912284+00:00
-- url     : https://prove2.me/theorems/efd14bb4-37d5-4309-b0f6-b7d8e556b937
-- title:
--   Near Bank Enumeration
-- statement:
--   Definitions and structural lemmas for Near Bank Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
set_option autoImplicit false
namespace ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)
def nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) := WeightedCache.near ![0,512,1025] Q D
def deficit {N : ℕ} (Q R : TritWord N) := WeightedCache.deficit ![0,512,1025] Q R
end ThreeSum.WeightedNearBankEnumeration


