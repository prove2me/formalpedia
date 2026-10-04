-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk0
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk0
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:10:46.180654+00:00
-- url     : https://prove2.me/theorems/9a671981-8505-4d1d-874d-4dc568c8587f
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
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell000__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell003__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell005__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell007__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell011__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell014__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell018__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell022__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell026__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell030__3

namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cells_blk_0 : ∀ i : Fin 256, i.val / 32 = 0 →
    DoubleCapBridgeDerivativeCellCertificate i
      doubleCapBridgeDerivativeExpression := by
  intro i h
  fin_cases i
  all_goals first | (exfalso; revert h; decide) | skip
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell000.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell001.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell002.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell003.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell004.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell005.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell006.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell007.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell008.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell009.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell010.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell011.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell012.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell013.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell014.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell015.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell016.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell017.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell019.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell020.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell021.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell022.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell023.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell024.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell025.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell026.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell027.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell028.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell029.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell030.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell031.acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative


