-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
-- name    : Submission_ThreeSum_TernaryOriginalAppendSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:33:05.170198+00:00
-- url     : https://prove2.me/theorems/cfa8b265-b9d4-4cf0-b98c-c8db84e9eecb
-- title:
--   Ternary Original Append Semantics
-- statement:
--   Definitions and structural lemmas for Ternary Original Append Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalAppendSemantics.lean

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryOriginalAppendSemantics
open Finset TernaryOriginalRowMenu TernaryExtensionEncoding
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 3000000
end ThreeSum.TernaryOriginalAppendSemantics


