-- Prove2me | Definitions.Def_Submission_Weighted_GlobalBank
-- name    : Submission_Weighted_GlobalBank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:13:23.010553+00:00
-- url     : https://prove2.me/theorems/36493c00-c3c9-45c6-bfc2-596d58235833
-- title:
--   Global Bank
-- statement:
--   Definitions and structural lemmas for Global Bank, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
namespace ThreeSum.WeightedGlobalBank
open TernaryJointType
abbrev rank {N : ℕ} (R : TritWord N) : ℕ := TernaryBank.rank R
abbrev Below {N : ℕ} (R Q : TritWord N) : Prop := TernaryBank.Below R Q
abbrev cacheCost {N : ℕ} (R : TritWord N) : ℕ := WeightedBankEnumeration.cacheCost R
abbrev bank (N T : ℕ) := WeightedBankEnumeration.bank N T
abbrev deficit {N : ℕ} (Q R : TritWord N) := WeightedNearBankEnumeration.deficit Q R
abbrev nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) := WeightedNearBankEnumeration.nearWords Q D
end ThreeSum.WeightedGlobalBank


