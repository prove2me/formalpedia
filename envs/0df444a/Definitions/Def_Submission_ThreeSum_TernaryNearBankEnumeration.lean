-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
-- name    : Submission_ThreeSum_TernaryNearBankEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:36:03.936234+00:00
-- url     : https://prove2.me/theorems/c8c624f2-eb71-4703-864a-3d790b6bab66
-- title:
--   Ternary Near Bank Enumeration
-- statement:
--   Definitions and structural lemmas for Ternary Near Bank Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
set_option autoImplicit false
namespace ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
end ThreeSum.TernaryNearBankEnumeration


