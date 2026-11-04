-- Prove2me | Definitions.Def_Submission_ThreeSum_ColorScan
-- name    : Submission_ThreeSum_ColorScan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:46:27.76073+00:00
-- url     : https://prove2.me/theorems/2d24d10a-f9d5-4c56-bfbf-22a243b5f39e
-- title:
--   Color Scan
-- statement:
--   Definitions and structural lemmas for Color Scan, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorScan.lean

import Definitions.Def_Submission_ThreeSum_ColorParameters
set_option autoImplicit false
namespace ThreeSum.ColorScan
open ColorParameters
def Hit {n : ℕ} (x : Fin n → ℤ) (W t : ℕ) : Prop :=
  ∃ i, ∃ hi : i < count W, i < t ∧ ColorClassLists.witness (parameter hi) x
end ThreeSum.ColorScan


