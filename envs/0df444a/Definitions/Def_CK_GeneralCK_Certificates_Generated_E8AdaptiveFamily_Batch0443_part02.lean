-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:55:09.136697+00:00
-- url     : https://prove2.me/theorems/406a7509-b624-45cf-adaa-28ad6f0ad258
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0443 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3548 : RatBall := localContactBall tau3548 center3548
def work3548 : RoundedTauEval :=
  evalTau precision tau3548 contact3548 logTwoBall

theorem center_sq3548 : (center3548.re : ℝ)^2 +
    (center3548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3548 : work3548.theta.ok = true ∧
    work3548.jac.invOK = true ∧ acceptsUnitSq work3548.out = true := by decide +kernel

def cell3548 : CellCertificate where
  tauBall := tau3548
  contactCenter := center3548
  contactBall := contact3548
  work := work3548
  center_sq := center_sq3548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3548.1
  jac_ok := checks3548.2.1
  accepted := checks3548.2.2

def tau3549 : RatBall :=
  ⟨⟨11/640, 253/640⟩, 3/1280⟩
def center3549 : GaussianRat :=
  ⟨7107163/500000000, 290339131/1000000000⟩
def contact3549 : RatBall := localContactBall tau3549 center3549
def work3549 : RoundedTauEval :=
  evalTau precision tau3549 contact3549 logTwoBall

theorem center_sq3549 : (center3549.re : ℝ)^2 +
    (center3549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3549 : work3549.theta.ok = true ∧
    work3549.jac.invOK = true ∧ acceptsUnitSq work3549.out = true := by decide +kernel

def cell3549 : CellCertificate where
  tauBall := tau3549
  contactCenter := center3549
  contactBall := contact3549
  work := work3549
  center_sq := center_sq3549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3549.1
  jac_ok := checks3549.2.1
  accepted := checks3549.2.2

def tau3550 : RatBall :=
  ⟨⟨9/640, 51/128⟩, 3/1280⟩
def center3550 : GaussianRat :=
  ⟨11666429/1000000000, 4577599/15625000⟩
def contact3550 : RatBall := localContactBall tau3550 center3550

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443


