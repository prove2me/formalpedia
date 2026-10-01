-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCertifiedLedgerBridge
-- name    : CK_GeneralCK_Certificates_E8TAxisCertifiedLedgerBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:07:02.099625+00:00
-- url     : https://prove2.me/theorems/c98178bb-fa5f-480d-bcf0-47e4ca76db62
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCertifiedLedgerBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisFirstCellCertified
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneratedGeometry

-- ===== source module GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge =====
section

/-! Identifies the certified first-cell theorem with its exact retained-ledger
record. -/

namespace GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge

open E8TAxisPartitionKernel E8TAxisGeneratedGeometry

theorem certifiedFirstCell_real :
    certifiedFirstCell.real = E8TAxisFirstCellCertified.rectangle := by
  congr 1 <;>
    norm_num [certifiedFirstCell, RatRect.real,
      E8TAxisFirstCellCertified.rectangle,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower]

theorem certifiedFirstCell_positive : CellPositive certifiedFirstCell.real := by
  rw [certifiedFirstCell_real]
  exact E8TAxisFirstCellCertified.cellPositive

#print axioms certifiedFirstCell_real
#print axioms certifiedFirstCell_positive

end GeneralCK.Certificates.E8TAxisCertifiedLedgerBridge

end


