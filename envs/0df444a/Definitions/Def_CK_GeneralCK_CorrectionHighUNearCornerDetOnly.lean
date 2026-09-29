-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerDetOnly
-- name    : CK_GeneralCK_CorrectionHighUNearCornerDetOnly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:42:59.107721+00:00
-- url     : https://prove2.me/theorems/3418ea39-1922-474e-9591-5a3533f36510
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerDetOnly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerDetOnly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerDetOnly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerDetOnly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerDetOnly.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerLeftMinor
import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerActualAdapter

/-! The accepted left-minor bound removes one of the raw corner premises. -/

namespace GeneralCK.Correction.HighU

def NearCornerDetWedgeTarget : Prop :=
  ∀ t rho : ℝ, 0 < t → t ≤ 1 / 100 → 0 < rho → rho ≤ 1 / 100 →
    (rho ≤ t →
      2 * rho ^ 2 * t ^ 9 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t)) ∧
    (t ≤ rho →
      2 * rho ^ 4 * t ^ 7 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t))

theorem nearCorner_rawWedges_of_detWedges
    (h : NearCornerDetWedgeTarget) : NearCornerRawWedgeTarget := by
  intro t rho ht ht1 hr hr1
  obtain ⟨hsmall, hlarge⟩ := h t rho ht ht1 hr hr1
  exact ⟨nearCorner_m11_lower ht ht1 hr hr1, hsmall, hlarge⟩

theorem nearCorner_actual_ratio_of_detWedges
    (h : NearCornerDetWedgeTarget) {t rho : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    ActualRatioMinorsPositive (1 / 2 - t) rho :=
  nearCorner_actual_ratio_of_raw_wedges
    (nearCorner_rawWedges_of_detWedges h) ht ht1 hr hr1

#print axioms nearCorner_rawWedges_of_detWedges
#print axioms nearCorner_actual_ratio_of_detWedges

end GeneralCK.Correction.HighU


