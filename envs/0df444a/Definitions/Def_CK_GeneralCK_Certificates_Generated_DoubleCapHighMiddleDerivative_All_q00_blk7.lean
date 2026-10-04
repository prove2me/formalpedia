-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:14:41.401443+00:00
-- url     : https://prove2.me/theorems/a1e72468-3849-4640-89a0-eb75d2088f9e
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
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell223__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell226__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell231__5
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell236__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell240__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell243__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell247__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell251__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell255

namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cells_blk_7 : ∀ i : Fin 256, i.val / 32 = 7 →
    DoubleCapBridgeDerivativeCellCertificate i
      doubleCapBridgeDerivativeExpression := by
  intro i h
  fin_cases i
  all_goals first | (exfalso; revert h; decide) | skip
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell224.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell225.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell226.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell227.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell228.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell229.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell230.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell231.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell232.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell233.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell234.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell235.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell236.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell237.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell238.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell239.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell240.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell241.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell242.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell243.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell244.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell245.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell246.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell247.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell248.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell249.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell250.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell251.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell252.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell253.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell254.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell255.acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative


