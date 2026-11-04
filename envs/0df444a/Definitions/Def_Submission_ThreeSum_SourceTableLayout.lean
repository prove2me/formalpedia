-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceTableLayout
-- name    : Submission_ThreeSum_SourceTableLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:46.776968+00:00
-- url     : https://prove2.me/theorems/7b37bf6a-5a8a-4092-864c-67a8e3a8d1ac
-- title:
--   Source Table Layout
-- statement:
--   Definitions and structural lemmas for Source Table Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceTableLayout.lean

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
set_option autoImplicit false
namespace ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
def maskAt (L cut i : ℕ) : ℕ := (enumerateDownset L cut).getD i 0
def setAt (L cut i : ℕ) : Finset (Fin L) := MaskDecode.decode L (maskAt L cut i)
end ThreeSum.SourceTableLayout


