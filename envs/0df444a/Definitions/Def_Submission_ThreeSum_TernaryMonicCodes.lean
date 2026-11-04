-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
-- name    : Submission_ThreeSum_TernaryMonicCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:28.655698+00:00
-- url     : https://prove2.me/theorems/4377e88c-f216-4f37-80b2-cff152d63193
-- title:
--   Ternary Monic Codes
-- statement:
--   Definitions and structural lemmas for Ternary Monic Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
def monicVector {d : ℕ} (a : Fin d → ZMod p) : Fin (d+1) → ZMod p :=
  Fin.lastCases 1 a
end ThreeSum.TernaryExtensionEncoding


