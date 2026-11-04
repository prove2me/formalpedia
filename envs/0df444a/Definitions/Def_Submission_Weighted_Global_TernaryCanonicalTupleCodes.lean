-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
-- name    : Submission_Weighted_Global_TernaryCanonicalTupleCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:02:20.93921+00:00
-- url     : https://prove2.me/theorems/a27530a5-6cf3-406b-8051-ec12f9d1bbf0
-- title:
--   Ternary Canonical Tuple Codes
-- statement:
--   Definitions and structural lemmas for Ternary Canonical Tuple Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000
end ThreeSum.WeightedGlobalCanonicalTupleCodes


