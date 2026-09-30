-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFullBiasTail8CurrentOwners
-- name    : CK_GeneralCK_PsiFullBiasTail8CurrentOwners
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:11:07.627333+00:00
-- url     : https://prove2.me/theorems/3613bf31-1500-4b3f-b237-60963fd68135
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFullBiasTail8CurrentOwners` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFullBiasTail8CurrentOwners` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFullBiasTail8CurrentOwners` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFullBiasTail8CurrentOwners (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFullBiasTail8CurrentOwners.lean)

import Definitions.Def_CK_GeneralCK_PsiCentralFullBiasWedges
import Definitions.Def_CK_GeneralCK_PsiSameSideTail8SmallMeanRegionClosure

-- ===== source module GeneralCK.PsiFullBiasTail8CurrentOwners =====
section

/-! Checked analytic psi owner interface after the full-bias central wedges. -/

namespace GeneralCK

structure PsiFullBiasTail8CurrentOwners : Prop where
  sameChart : SameSidePsiTail8SmallMeanChartOwner
  oppositeCentral : PsiCentralFullBiasWedges.CentralOwner
  oppositeCompact : PsiThreeTenthsTail28.CompactOwner

theorem PsiFullBiasTail8CurrentOwners.toTail37Central
    (h : PsiFullBiasTail8CurrentOwners) :
    PsiThreeTenthsCentralTail37.CentralOwner :=
  PsiThreeTenthsTail28.toTail37CentralOwner
    (PsiCentralSixteenWedge.toTail28CentralOwner
      (PsiCentralTwentyFourWedge.toSixteenCentralOwner
        (PsiCentralFullBiasWedges.toTwentyFourCentralOwner
          h.oppositeCentral)))

theorem PsiFullBiasTail8CurrentOwners.toTail14Same
    (h : PsiFullBiasTail8CurrentOwners) :
    SameSidePsiTail14ExtendedChartOwner :=
  sameSidePsiTail14ExtendedChartOwner_of_tail8SmallMean h.sameChart

theorem PsiFullBiasTail8CurrentOwners.toThreeTenthsCompact
    (h : PsiFullBiasTail8CurrentOwners) :
    PsiThreeTenthsBias.CompactOwner :=
  PsiThreeTenthsTail28.toThreeTenthsCompactOwner h.oppositeCompact

#print axioms PsiFullBiasTail8CurrentOwners.toTail37Central
#print axioms PsiFullBiasTail8CurrentOwners.toTail14Same
#print axioms PsiFullBiasTail8CurrentOwners.toThreeTenthsCompact

end GeneralCK

end


