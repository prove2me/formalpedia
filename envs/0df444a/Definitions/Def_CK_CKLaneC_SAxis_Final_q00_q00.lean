-- Prove2me | Definitions.Def_CK_CKLaneC_SAxis_Final_q00_q00
-- name    : CK_CKLaneC_SAxis_Final_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T17:25:14.711035+00:00
-- url     : https://prove2.me/theorems/e3d8c2ca-2d59-42d3-8460-5d9e75a5b7ca
-- title:
--   Courtade–Kumar proof module `CKLaneC.SAxis.Final (piece 1 of 3) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.SAxis.Final (piece 1 of 3) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.SAxis.Final (piece 1 of 3) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.SAxis.Final (piece 1 of 3) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/SAxis/Final (piece 1 of 3) (piece 1 of 2).lean)

import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells00
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells01
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells02
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells03
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells04
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells05
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells06
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells07
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells08
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells09
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells10
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells11
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells12
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells13
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells14
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells15
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells16
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells17
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells18
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells19
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells20
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells21
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells22
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells23
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells24
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells25
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells26
import Definitions.Def_CK_CKLaneC_SAxis_Data_Cells27
import Definitions.Def_CK_GeneralCK_PureGapE8SAxisTailSixteen




/-!
# Lane C: the E8 s-axis region (unconditional)

Corner-monotone cubic/quadratic/linear Taylor cells (`CKLaneC.SAxis.Cell`) over a checked slope
table (`CKLaneC.SAxis.Data.T`) and the regular source polynomial cover the strip
`0 < s ≤ 1/50`, `3/50 ≤ t < 16`, `2/25 < s + t`, proving
`GeneralCK.E8SAxisDerivativeRemainderSixteen`, hence the `sAxis` field of
`E8CertificateOwners` via `GeneralCK.e8_sAxis_of_sixteen_remainder`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open CKLaneC.S3.SlopeTable CKLaneC.S3.SlopeChain CKLaneC.SAxis.Cell CKLaneC.SAxis.Data

namespace CKLaneC.SAxis.Final

/-- All certified cells. -/
def cells : List CellW := (cells00 ++ (cells01 ++ (cells02 ++ (cells03 ++ (cells04 ++ (cells05 ++ (cells06 ++ (cells07 ++ (cells08 ++ (cells09 ++ (cells10 ++ (cells11 ++ (cells12 ++ (cells13 ++ (cells14 ++ (cells15 ++ (cells16 ++ (cells17 ++ (cells18 ++ (cells19 ++ (cells20 ++ (cells21 ++ (cells22 ++ (cells23 ++ (cells24 ++ (cells25 ++ (cells26 ++ (cells27 ++ []))))))))))))))))))))))))))))

end CKLaneC.SAxis.Final


