-- Prove2me | Definitions.Def_CK_GeneralCK_PsiAfterCornerClosure
-- name    : CK_GeneralCK_PsiAfterCornerClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:13:11.320841+00:00
-- url     : https://prove2.me/theorems/e7a8e2df-2eda-4f18-b47e-d21167e11555
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiAfterCornerClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiAfterCornerClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiAfterCornerClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiAfterCornerClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiAfterCornerClosure.lean)

import Definitions.Def_CK_GeneralCK_PsiAfterTailClosure
import Definitions.Def_CK_GeneralCK_PsiEndpointBellman
import Definitions.Def_CK_GeneralCK_PsiOppositeBoundaryOwner
import Definitions.Def_CK_GeneralCK_PsiOppositeLowEntropyOwner

-- ===== source module GeneralCK.PsiAfterCornerClosure =====
section

/-!
# Residual active-psi interface after the analytic endpoint argument

The same-side ratio tail, opposite deterministic corner, opposite boundary,
and global opposite low-entropy region are proved. The successive interfaces
below preserve the earlier APIs; the final interface has three owner fields.
-/

namespace GeneralCK

structure ResidualPsiCertificateOwnersExceptRatioTailCorner : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeBoundary : OppositePsiBoundaryOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

/-- Restore the previous owner interface using the proved corner inequality.
Keeping this constructor separate preserves the earlier closure APIs. -/
theorem ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwnersExceptRatioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ResidualPsiCertificateOwnersExceptRatioTail where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := h.oppositeBoundary
  oppositeCorner := oppositePsiCornerOwner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwners
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ResidualPsiCertificateOwners :=
  h.toOwnersExceptRatioTail.toOwners

theorem residualPsi_of_certificateOwners_after_ratioTail_corner
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

/-- Four fields remain after the full opposite boundary is also discharged. -/
structure ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTailCorner
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ResidualPsiCertificateOwnersExceptRatioTailCorner where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := oppositePsiBoundaryOwner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ResidualPsiCertificateOwnersExceptRatioTail :=
  h.toOwnersExceptRatioTailCorner.toOwnersExceptRatioTail

theorem residualPsi_of_certificateOwners_after_endpoint_analytic
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

/-- The three active-psi regions remaining after the analytic endpoint and
retained-child arguments. Each field keeps the original exact ledger domain. -/
structure ResidualPsiAnalyticRemainingOwners : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiAnalyticRemainingOwners.toOwnersExceptRatioTailCornerBoundary
    (h : ResidualPsiAnalyticRemainingOwners) :
    ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeLowEntropy := oppositePsiLowEntropyOwner
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiAnalyticRemainingOwners.toOwnersExceptRatioTail
    (h : ResidualPsiAnalyticRemainingOwners) :
    ResidualPsiCertificateOwnersExceptRatioTail :=
  h.toOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTail

theorem residualPsi_of_analytic_remaining_owners
    (h : ResidualPsiAnalyticRemainingOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

end GeneralCK

#print axioms GeneralCK.ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwnersExceptRatioTail
#print axioms GeneralCK.residualPsi_of_certificateOwners_after_ratioTail_corner
#print axioms GeneralCK.residualPsi_of_certificateOwners_after_endpoint_analytic
#print axioms GeneralCK.residualPsi_of_analytic_remaining_owners

end


