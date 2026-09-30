-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:15.096611+00:00
-- url     : https://prove2.me/theorems/e52294ea-9609-4ff4-9852-b553e4dea5b9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0443 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3544 : RatBall :=
  ⟨⟨13/640, 249/640⟩, 3/1280⟩
def center3544 : GaussianRat :=
  ⟨3339277/200000000, 71285531/250000000⟩
def contact3544 : RatBall := localContactBall tau3544 center3544
def work3544 : RoundedTauEval :=
  evalTau precision tau3544 contact3544 logTwoBall

theorem center_sq3544 : (center3544.re : ℝ)^2 +
    (center3544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3544 : work3544.theta.ok = true ∧
    work3544.jac.invOK = true ∧ acceptsUnitSq work3544.out = true := by decide +kernel

def cell3544 : CellCertificate where
  tauBall := tau3544
  contactCenter := center3544
  contactBall := contact3544
  work := work3544
  center_sq := center_sq3544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3544.1
  jac_ok := checks3544.2.1
  accepted := checks3544.2.2

def tau3545 : RatBall :=
  ⟨⟨3/128, 249/640⟩, 3/1280⟩
def center3545 : GaussianRat :=
  ⟨19263193/1000000000, 142544269/500000000⟩
def contact3545 : RatBall := localContactBall tau3545 center3545
def work3545 : RoundedTauEval :=
  evalTau precision tau3545 contact3545 logTwoBall

theorem center_sq3545 : (center3545.re : ℝ)^2 +
    (center3545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3545 : work3545.theta.ok = true ∧
    work3545.jac.invOK = true ∧ acceptsUnitSq work3545.out = true := by decide +kernel

def cell3545 : CellCertificate where
  tauBall := tau3545
  contactCenter := center3545
  contactBall := contact3545
  work := work3545
  center_sq := center_sq3545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3545.1
  jac_ok := checks3545.2.1
  accepted := checks3545.2.2

def tau3546 : RatBall :=
  ⟨⟨13/640, 251/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443


