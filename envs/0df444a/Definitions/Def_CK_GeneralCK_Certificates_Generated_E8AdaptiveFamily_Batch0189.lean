-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:17:52.006824+00:00
-- url     : https://prove2.me/theorems/d4adf13c-cb6a-4e0d-85c1-bf2a8a48f74b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0189.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1519 : RatBall := localContactBall tau1519 center1519
def work1519 : RoundedTauEval :=
  evalTau precision tau1519 contact1519 logTwoBall

theorem center_sq1519 : (center1519.re : ℝ)^2 +
    (center1519.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1519]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1519 : work1519.theta.ok = true ∧
    work1519.jac.invOK = true ∧ acceptsUnitSq work1519.out = true := by decide +kernel

def cell1519 : CellCertificate where
  tauBall := tau1519
  contactCenter := center1519
  contactBall := contact1519
  work := work1519
  center_sq := center_sq1519
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1519.1
  jac_ok := checks1519.2.1
  accepted := checks1519.2.2

def cells : List CellCertificate := [cell1512, cell1513, cell1514, cell1515, cell1516, cell1517, cell1518, cell1519]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189


