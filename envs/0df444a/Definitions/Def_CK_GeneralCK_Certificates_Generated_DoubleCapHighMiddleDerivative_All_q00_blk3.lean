-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk3
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:17:52.784927+00:00
-- url     : https://prove2.me/theorems/449091fe-cd89-4109-a331-b93461702d0f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.All (proof part: 32-cell block)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.All (proof part: 32-cell block)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.All (proof part: 32-cell block)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.All (proof part: 32-cell block) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/All (proof part: 32-cell block).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeValueAdapter
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell095__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell098__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell102__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell105__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell109__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell112__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell115__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell117__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell121__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell125__3

namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cells_blk_3 : ∀ i : Fin 256, i.val / 32 = 3 →
    DoubleCapBridgeDerivativeCellCertificate i
      doubleCapBridgeDerivativeExpression := by
  intro i h
  fin_cases i
  all_goals first | (exfalso; revert h; decide) | skip
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell096.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell097.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell098.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell099.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell100.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell101.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell102.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell103.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell104.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell105.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell106.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell107.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell108.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell109.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell110.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell111.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell112.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell113.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell114.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell115.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell116.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell117.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell118.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell119.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell120.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell121.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell122.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell123.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell124.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell125.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell126.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell127.acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative


