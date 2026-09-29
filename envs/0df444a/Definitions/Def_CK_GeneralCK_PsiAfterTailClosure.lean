-- Prove2me | Definitions.Def_CK_GeneralCK_PsiAfterTailClosure
-- name    : CK_GeneralCK_PsiAfterTailClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:05:47.733581+00:00
-- url     : https://prove2.me/theorems/d28c4686-0dec-4bee-8b36-6a8df7e2c42e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiAfterTailClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiAfterTailClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiAfterTailClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiAfterTailClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiAfterTailClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiSameRatioTail

-- ===== source module GeneralCK.PsiAfterTailClosure =====
section

/-! The exact residual active-psi interface after the uniform ratio tail. -/

namespace GeneralCK

/-- Six mathematical owners remain after the completed same-side ratio tail.
These fields retain their exact domains from `PsiRegionLedger`. -/
structure ResidualPsiCertificateOwnersExceptRatioTail : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeBoundary : OppositePsiBoundaryOwner
  oppositeCorner : OppositePsiCornerOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiCertificateOwnersExceptRatioTail.toOwners
    (h : ResidualPsiCertificateOwnersExceptRatioTail) :
    ResidualPsiCertificateOwners where
  sameRatioTail := sameSidePsiRatioTailOwner
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := h.oppositeBoundary
  oppositeCorner := h.oppositeCorner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem residualPsi_of_certificateOwners_after_ratioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTail) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners h.toOwners

#print axioms ResidualPsiCertificateOwnersExceptRatioTail.toOwners
#print axioms residualPsi_of_certificateOwners_after_ratioTail

end GeneralCK

end


