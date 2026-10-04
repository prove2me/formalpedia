-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk4
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:14:29.429362+00:00
-- url     : https://prove2.me/theorems/71aa4f1f-c9f6-4622-b586-1db83b814bd4
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
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell128__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell131__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell135__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell138__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell141__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell143__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell147__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell149__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell151__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell154__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell158__2

namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cells_blk_4 : ∀ i : Fin 256, i.val / 32 = 4 →
    DoubleCapBridgeDerivativeCellCertificate i
      doubleCapBridgeDerivativeExpression := by
  intro i h
  fin_cases i
  all_goals first | (exfalso; revert h; decide) | skip
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell128.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell129.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell130.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell131.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell132.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell133.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell134.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell136.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell138.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell139.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell140.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell141.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell142.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell143.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell144.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell145.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell146.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell147.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell148.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell149.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell150.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell151.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell152.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell153.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell154.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell155.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell156.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell157.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell158.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell159.acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative


