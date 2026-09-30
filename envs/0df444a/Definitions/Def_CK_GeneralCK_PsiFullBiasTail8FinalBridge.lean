-- Prove2me | Definitions.Def_CK_GeneralCK_PsiFullBiasTail8FinalBridge
-- name    : CK_GeneralCK_PsiFullBiasTail8FinalBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:11:36.562126+00:00
-- url     : https://prove2.me/theorems/332e82c9-5f01-4052-9509-9a2d1675385d
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiFullBiasTail8FinalBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiFullBiasTail8FinalBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiFullBiasTail8FinalBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiFullBiasTail8FinalBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiFullBiasTail8FinalBridge.lean)

import Definitions.Def_CK_GeneralCK_PsiFullBiasTail8CurrentOwners
import Definitions.Def_CK_GeneralCK_PsiExtendedRegionClosure
import Definitions.Def_CK_GeneralCK_FinalAssemblyAfterDiagnosticHybrid

-- ===== source module GeneralCK.PsiFullBiasTail8FinalBridge =====
section

/-!
# Direct final-owner bridge for the current active-Psi frontier

This file isolates the active-Psi dependency from the other production
families.  The three fields in `PsiFullBiasTail8CurrentOwners` are exactly
the current strict residual regions.  All of the regions deleted on the way
back to the canonical active-Psi statement are restored by the checked
analytic theorems in the existing conversion chain.
-/

namespace GeneralCK

/-- Restore the canonical three-chart interface from the exact current
frontier.  Each conversion consumes a previously proved closed region. -/
theorem PsiFullBiasTail8CurrentOwners.toExtendedRemainingOwners
    (h : PsiFullBiasTail8CurrentOwners) : ResidualPsiExtendedRemainingOwners where
  sameChart := sameSidePsiExtendedChartOwner_of_tail16
    (sameSidePsiTail16ChartOwner_of_tail15
      (sameSidePsiTail15ChartOwner_of_tail14Extended h.toTail14Same))
  oppositeCentral := PsiCentralAnalytic.toExtendedCentralOwner
    (PsiEntropy200.toCentralAnalyticOwner
      (PsiEighthBias.toEntropy200CentralOwner
        (PsiSeventhBias.toEighthCentralOwner
          (PsiSixthBias.toSeventhCentralOwner
            (PsiFifthBias.toSixthCentralOwner
              (PsiFifthBiasAutomatic.toFifthCentralOwner
                (PsiQuarterBias.toAutomaticCentralOwner
                  (PsiTwoSeventhsBias.toQuarterCentralOwner
                    (PsiThreeTenthsBias.toTwoSeventhsCentralOwner
                      (PsiThreeTenthsCentralTail40.toThreeTenthsCentralOwner
                        (PsiThreeTenthsCentralTail37.toTail40CentralOwner
                          h.toTail37Central)))))))))))
  oppositeCompact := PsiCompactAnalytic.toExtendedCompactOwner
    (PsiEntropy200.toCompactAnalyticOwner
      (PsiEighthBias.toEntropy200CompactOwner
        (PsiSeventhBias.toEighthCompactOwner
          (PsiSixthBias.toSeventhCompactOwner
            (PsiFifthBias.toSixthCompactOwner
              (PsiFifthBiasAutomatic.toFifthCompactOwner
                (PsiQuarterBias.toAutomaticCompactOwner
                  (PsiTwoSeventhsBias.toQuarterCompactOwner
                    (PsiThreeTenthsBias.toTwoSeventhsCompactOwner
                      h.toThreeTenthsCompact)))))))))

/-- The current three residual owners imply the exact actual-law Psi theorem
used by the final hybrid assembly.  It is stated without importing the much
larger final-assembly closure. -/
theorem residualPsi_of_fullBiasTail8CurrentOwners
    (h : PsiFullBiasTail8CurrentOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_extended_remaining_owners h.toExtendedRemainingOwners

/-- Final-assembly adapter.  Its target is definitionally the preceding
actual-law theorem, so it introduces no additional analytic premise. -/
theorem PsiFullBiasTail8CurrentOwners.toRemainingPsiHybridOwner
    (h : PsiFullBiasTail8CurrentOwners) :
    HybridAfterDiagnostic.RemainingPsiHybridOwner :=
  residualPsi_of_fullBiasTail8CurrentOwners h

#print axioms PsiFullBiasTail8CurrentOwners.toExtendedRemainingOwners
#print axioms residualPsi_of_fullBiasTail8CurrentOwners
#print axioms PsiFullBiasTail8CurrentOwners.toRemainingPsiHybridOwner

end GeneralCK

end


