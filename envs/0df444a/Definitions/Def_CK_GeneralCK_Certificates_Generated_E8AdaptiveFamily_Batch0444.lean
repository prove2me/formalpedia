-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:46:37.01198+00:00
-- url     : https://prove2.me/theorems/d813a5a1-0772-45a8-885b-2a1541962bb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0444.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3559 : GaussianRat :=
  ⟨1839637/62500000, 141119723/500000000⟩
def contact3559 : RatBall := localContactBall tau3559 center3559
def work3559 : RoundedTauEval :=
  evalTau precision tau3559 contact3559 logTwoBall

theorem center_sq3559 : (center3559.re : ℝ)^2 +
    (center3559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3559 : work3559.theta.ok = true ∧
    work3559.jac.invOK = true ∧ acceptsUnitSq work3559.out = true := by decide +kernel

def cell3559 : CellCertificate where
  tauBall := tau3559
  contactCenter := center3559
  contactBall := contact3559
  work := work3559
  center_sq := center_sq3559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3559.1
  jac_ok := checks3559.2.1
  accepted := checks3559.2.2

def cells : List CellCertificate := [cell3552, cell3553, cell3554, cell3555, cell3556, cell3557, cell3558, cell3559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444


