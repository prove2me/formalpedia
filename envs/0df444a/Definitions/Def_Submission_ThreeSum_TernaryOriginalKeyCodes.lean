-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
-- name    : Submission_ThreeSum_TernaryOriginalKeyCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:28:45.878976+00:00
-- url     : https://prove2.me/theorems/500a510c-23f7-4223-996f-db5d73c62019
-- title:
--   Ternary Original Key Codes
-- statement:
--   Definitions and structural lemmas for Ternary Original Key Codes, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalKeyCodes.lean

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_involutive
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt

set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
def appendVector {r : ℕ} (v : Fin r → ZMod p) (a : ZMod p) : Fin (r+1) → ZMod p :=
  Fin.lastCases a v
def digitOrder (J : ℕ) : Fin (J+2) ≃ Fin (J+2) where
  toFun i := ⟨TernarySignedLayout.offset J i.val,TernarySignedLayout.offset_lt i.isLt⟩
  invFun i := ⟨TernarySignedLayout.offset J i.val,TernarySignedLayout.offset_lt i.isLt⟩
  left_inv i := Fin.ext (TernarySignedLayout.offset_involutive i.isLt)
  right_inv i := Fin.ext (TernarySignedLayout.offset_involutive i.isLt)
variable {f : (ZMod p)[X]} [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
end ThreeSum.TernaryExtensionEncoding


