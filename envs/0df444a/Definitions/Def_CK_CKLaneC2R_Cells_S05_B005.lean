-- Prove2me | Definitions.Def_CK_CKLaneC2R_Cells_S05_B005
-- name    : CK_CKLaneC2R_Cells_S05_B005
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:24:48.256856+00:00
-- url     : https://prove2.me/theorems/a4b2d516-f4c3-44ba-afc5-874d7589a155
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.Cells.S05.B005` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.Cells.S05.B005` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.Cells.S05.B005` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.Cells.S05.B005 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/Cells/S05/B005.lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S05_B005_part01

namespace CKLaneC2R.Cells.S05.B005

open GeneralCK GeneralCK.Certificates CKLaneC2R ReflectionCompactProgramKernel CKLaneC2R.T

-- box ['15489/16000', '3897/4000', '217/400', '9593/16000']  taylor_lower 76340627503167933129843/225179981368524800000
theorem c119_ok : cellOkT c119 = true := by decide +kernel
theorem c119_pos {a z : ℝ} (ha1 : ((9/10 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((7299/8000 : ℚ) : ℝ))
    (hz1 : ((2649/3200 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((27403/32000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  cellOkT_sound c119 c119_ok ha1 ha2 hz1 hz2

end CKLaneC2R.Cells.S05.B005


