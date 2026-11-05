-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:07:22.145324+00:00
-- url     : https://prove2.me/theorems/a283f0d7-3703-41ee-b548-474296bdb6d0
-- title:
--   NearBankEnumeration
-- statement:
--   Definitions and structural lemmas for NearBankEnumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearBankEnumeration.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)
def nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) := WeightedCache.near ![0,1369,2740] Q D
def deficit {N : ℕ} (Q R : TritWord N) := WeightedCache.deficit ![0,1369,2740] Q R
end ThreeSum.WeightedNearBankEnumeration
end WeightedCache3SUMRefinement_e1ae71d


