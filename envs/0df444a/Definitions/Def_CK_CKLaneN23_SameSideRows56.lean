-- Prove2me | Definitions.Def_CK_CKLaneN23_SameSideRows56
-- name    : CK_CKLaneN23_SameSideRows56
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T01:17:13.127448+00:00
-- url     : https://prove2.me/theorems/e11ed16a-c4db-4a93-914d-0822aefd851f
-- title:
--   Courtade–Kumar proof module `CKLaneN23.SameSideRows56` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.SameSideRows56` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.SameSideRows56` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.SameSideRows56 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/SameSideRows56.lean)

import Definitions.Def_CK_CKLaneN23_Row6Strip

-- ===== source module CKLaneN23.SameSideRows56 =====
section

/-!
# Lane N23 — rows 5 and 6 plugged into the same-side interface

Conditional adapters (NOT closures): `SR_SameSideHalf` from the remaining six certificate rows
and `SR_DiagonalBand` from the remaining four, with rows 5 (`NoSepA_HighBiasRem`) and
6 (`NoSepA_StripRem`) discharged unconditionally by `Row5.row_noSepA_highBiasRem` and
`Row6.row_noSepA_stripRem`.
-/

namespace CKLaneN23

/-- Conditional (NOT a closure): rows 1–4, 7, 8 imply `SR_SameSideHalf`. -/
theorem sameSideHalf_of_remaining_six_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest)
    (hNear : SmallRatioT3NearRest) (hFE : FullEntropySSCoverRest) : SR_SameSideHalf :=
  sameSideHalf_of_certificate_rows hT1 hT4 hcap hMod Row5.row_noSepA_highBiasRem
    Row6.row_noSepA_stripRem hNear hFE

/-- Conditional (NOT a closure): rows 1–4 imply `SR_DiagonalBand`. -/
theorem diagonalBand_of_remaining_four_rows (hT1 : SmallRatioT1Cover)
    (hT4 : SmallRatioT4Rest) (hcap : CentralCap) (hMod : NoSepA_ModerateRest) :
    SR_DiagonalBand :=
  diagonalBand_of_certificate_rows hT1 hT4 hcap hMod Row5.row_noSepA_highBiasRem
    Row6.row_noSepA_stripRem

end CKLaneN23

end


