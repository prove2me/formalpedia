-- Prove2me | Definitions.Def_Submission_ThreeSum_TernarySignedLayout
-- name    : Submission_ThreeSum_TernarySignedLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:18:58.88522+00:00
-- url     : https://prove2.me/theorems/10ff89a5-c8f7-468a-ab23-cd773fb94c70
-- title:
--   Ternary Signed Layout
-- statement:
--   Definitions and structural lemmas for Ternary Signed Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedLayout.lean

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
set_option autoImplicit false
namespace ThreeSum.TernarySignedLayout
open TernarySignedReduction
def offset (J i : ℕ) : ℕ := if i<J then J-1-i else i
def feature {J : ℕ} (f : Coordinate J→ℤ) (i : ℕ) : ℤ :=
  if h : i<J then f (.inl ⟨i,h⟩) else if i=J then f (.inr false) else f (.inr true)
end ThreeSum.TernarySignedLayout


