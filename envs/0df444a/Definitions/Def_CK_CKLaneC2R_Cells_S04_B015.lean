-- Prove2me | Definitions.Def_CK_CKLaneC2R_Cells_S04_B015
-- name    : CK_CKLaneC2R_Cells_S04_B015
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T08:33:53.908894+00:00
-- url     : https://prove2.me/theorems/2ccb8a54-1579-4a47-b884-99619e0050e1
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.Cells.S04.B015` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.Cells.S04.B015` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.Cells.S04.B015` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.Cells.S04.B015 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/Cells/S04/B015.lean)

import Definitions.Def_CK_CKLaneC2R_Cells_S04_B015_part01

namespace CKLaneC2R.Cells.S04.B015

open GeneralCK GeneralCK.Certificates CKLaneC2R ReflectionCompactProgramKernel CKLaneC2R.T

-- box ['67/80', '17/20', '61197/64000', '6211/6400']  taylor_lower 224502806785037361831823/36028797018963968000000
theorem c319_ok : cellOkT c319 = true := by decide +kernel
theorem c319_pos {a z : ℝ} (ha1 : ((31/40 : ℚ) : ℝ) ≤ a) (ha2 : a ≤ ((63/80 : ℚ) : ℝ))
    (hz1 : ((63023/64000 : ℚ) : ℝ) ≤ z) (hz2 : z ≤ ((126959/128000 : ℚ) : ℝ)) :
    0 < GeneralCK.Reflection.curvature a (a * z) :=
  cellOkT_sound c319 c319_ok ha1 ha2 hz1 hz2

end CKLaneC2R.Cells.S04.B015


