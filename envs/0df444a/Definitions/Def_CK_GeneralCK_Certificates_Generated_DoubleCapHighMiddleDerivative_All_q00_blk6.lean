-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk6
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_All_q00_blk6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T07:17:48.869402+00:00
-- url     : https://prove2.me/theorems/0fd68403-4f78-4ee9-9278-1aa0046c989f
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
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell192__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell196__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell200__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell203__2
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell205__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell209__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell213__4
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell217__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell220__3
import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell223__3

namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cells_blk_6 : ∀ i : Fin 256, i.val / 32 = 6 →
    DoubleCapBridgeDerivativeCellCertificate i
      doubleCapBridgeDerivativeExpression := by
  intro i h
  fin_cases i
  all_goals first | (exfalso; revert h; decide) | skip
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell192.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell193.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell194.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell195.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell196.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell197.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell198.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell199.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell200.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell201.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell202.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell203.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell204.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell205.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell206.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell207.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell208.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell209.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell210.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell211.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell212.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell213.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell215.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell216.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell217.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell218.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell219.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell220.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell221.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell222.acceptedCell
  · exact GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell223.acceptedCell

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative


