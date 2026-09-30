-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:27.813429+00:00
-- url     : https://prove2.me/theorems/ff4838d9-bde5-4902-b75e-043f5a126ad4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0467.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3742 : work3742.theta.ok = true ∧
    work3742.jac.invOK = true ∧ acceptsUnitSq work3742.out = true := by decide +kernel

def cell3742 : CellCertificate where
  tauBall := tau3742
  contactCenter := center3742
  contactBall := contact3742
  work := work3742
  center_sq := center_sq3742
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3742.1
  jac_ok := checks3742.2.1
  accepted := checks3742.2.2

def tau3743 : RatBall :=
  ⟨⟨93/640, 237/640⟩, 3/1280⟩
def center3743 : GaussianRat :=
  ⟨115826349/1000000000, 52528557/200000000⟩
def contact3743 : RatBall := localContactBall tau3743 center3743
def work3743 : RoundedTauEval :=
  evalTau precision tau3743 contact3743 logTwoBall

theorem center_sq3743 : (center3743.re : ℝ)^2 +
    (center3743.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3743]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3743 : work3743.theta.ok = true ∧
    work3743.jac.invOK = true ∧ acceptsUnitSq work3743.out = true := by decide +kernel

def cell3743 : CellCertificate where
  tauBall := tau3743
  contactCenter := center3743
  contactBall := contact3743
  work := work3743
  center_sq := center_sq3743
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3743.1
  jac_ok := checks3743.2.1
  accepted := checks3743.2.2

def cells : List CellCertificate := [cell3736, cell3737, cell3738, cell3739, cell3740, cell3741, cell3742, cell3743]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467


