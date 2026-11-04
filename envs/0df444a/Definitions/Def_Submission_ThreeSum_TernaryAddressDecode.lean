-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
-- name    : Submission_ThreeSum_TernaryAddressDecode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:56:40.875689+00:00
-- url     : https://prove2.me/theorems/aa255f0e-ad2c-4cd9-b456-c4e3394d04ef
-- title:
--   Ternary Address Decode
-- statement:
--   Definitions and structural lemmas for Ternary Address Decode, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddressDecode.lean

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_LightTernaryCodes_digit_le_two
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace ThreeSum.TernaryAddressDecode
open TernaryJointType TernaryCodeSemantics
def word (N code : ℕ) : TritWord N := fun i =>
  ⟨LightTernaryCodes.digit (2*N) (low i) (high i) code,
    Nat.lt_succ_of_le (LightTernaryCodes.digit_le_two _ _ _ _)⟩
end ThreeSum.TernaryAddressDecode


