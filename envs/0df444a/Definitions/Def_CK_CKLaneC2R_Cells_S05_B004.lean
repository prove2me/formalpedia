-- Prove2me | Definitions.Def_CK_CKLaneC2R_Cells_S05_B004
-- name    : CK_CKLaneC2R_Cells_S05_B004
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:43:49.39481+00:00
-- url     : https://prove2.me/theorems/c516650a-04eb-4bbc-a51e-d832e0f5b087
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.Cells.S05.B004` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.Cells.S05.B004` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.Cells.S05.B004` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.Cells.S05.B004 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/Cells/S05/B004.lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B004_part01

namespace CKLaneC2R.Cells.S05.B004

open GeneralCK GeneralCK.Certificates CKLaneC2R ReflectionCompactProgramKernel CKLaneC2R.T

-- box ['31473/32000', '7893/8000', '1601/8000', '1257/4000']  taylor_lower 2044584340414497082450589/4503599627370496000000
theorem c99_ok : cellOkT c99 = true := by decide +kernel
theorem c99_pos {a z : ℝ} (ha1 : ((1539/1600 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((15489/16000 : ℚ) : ℝ))
    (hz1 : ((217/400 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((9593/16000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  cellOkT_sound c99 c99_ok ha1 ha2 hz1 hz2

end CKLaneC2R.Cells.S05.B004


