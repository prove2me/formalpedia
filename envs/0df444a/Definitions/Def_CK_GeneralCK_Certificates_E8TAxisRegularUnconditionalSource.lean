-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularUnconditionalSource
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:45:18.559026+00:00
-- url     : https://prove2.me/theorems/1cbec3ad-4c0e-43e0-b765-e703d04f3602
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularUnconditionalSource` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularUnconditionalSource` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularUnconditionalSource` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularUnconditionalSource (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularUnconditionalSource.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularDyadicEvaluator
import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate

-- ===== source module GeneralCK.Certificates.E8TAxisRegularUnconditionalSource =====
section

/-! The zero-endpoint source evaluator specialized to the completed, kernel-checked
complex derivative certificate. No production Lipschitz premise remains. -/

namespace GeneralCK.Certificates.E8TAxisRegularUnconditionalSource
open Set Metric DyadicInterval E8TauInverseContraction
open E8TAxisRegularGermJet E8TAxisRegularDyadicEvaluator

theorem remainder_lipschitz :
    LipschitzOnWith (1 : NNReal) thetaTauRemainder (closedBall 0 tauRadius) := by
  exact E8ThetaTauAnalytic.thetaTauRemainder_lipschitz_of_deriv_bound
    (E8ThetaTauDerivativeFormula.final_derivative_bound_of_expr_bound
      Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound)

theorem regularJetBox_contains {p : ℕ} {box : DyadicInterval p} {y : ℝ}
    (hy : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularJetBox box).Contains regularQJet y :=
  regularJetBox_sound remainder_lipschitz hy hy0 hyUpper

theorem regularComponentBox_contains {p : ℕ} {box : DyadicInterval p}
    {y : ℝ} (j : ℕ) (hj : j ≤ 5)
    (hy : box.Contains y) (hy0 : 0 ≤ y) (hyUpper : y ≤ 4 / 25) :
    (regularComponentBox j box).Contains
      (E8TAxisRegularSourceBounds.component regularQJet j y) :=
  regularComponentBox_sound remainder_lipschitz j hj hy hy0 hyUpper

#print axioms remainder_lipschitz
#print axioms regularJetBox_contains
#print axioms regularComponentBox_contains
end GeneralCK.Certificates.E8TAxisRegularUnconditionalSource

end


