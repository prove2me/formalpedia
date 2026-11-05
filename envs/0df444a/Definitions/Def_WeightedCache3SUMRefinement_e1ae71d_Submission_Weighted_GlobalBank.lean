-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:09:16.95795+00:00
-- url     : https://prove2.me/theorems/30b8cf08-0806-4d59-b9da-af3afcc261f6
-- title:
--   GlobalBank
-- statement:
--   Definitions and structural lemmas for GlobalBank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedGlobalBank
open TernaryJointType
abbrev rank {N : ℕ} (R : TritWord N) : ℕ := TernaryBank.rank R
abbrev Below {N : ℕ} (R Q : TritWord N) : Prop := TernaryBank.Below R Q
abbrev cacheCost {N : ℕ} (R : TritWord N) : ℕ := WeightedBankEnumeration.cacheCost R
abbrev bank (N T : ℕ) := WeightedBankEnumeration.bank N T
abbrev deficit {N : ℕ} (Q R : TritWord N) := WeightedNearBankEnumeration.deficit Q R
abbrev nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) := WeightedNearBankEnumeration.nearWords Q D
end ThreeSum.WeightedGlobalBank
end WeightedCache3SUMRefinement_e1ae71d


