-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
-- name    : Submission_ThreeSum_TernaryExtensionDecoded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:58:20.471049+00:00
-- url     : https://prove2.me/theorems/45f24741-3fc1-4f9b-993c-7b6f9fb6cf8f
-- title:
--   Ternary Extension Decoded
-- statement:
--   Definitions and structural lemmas for Ternary Extension Decoded, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionDecoded.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
end ThreeSum.TernaryExtensionEncoding


