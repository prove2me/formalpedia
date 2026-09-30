-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:52:52.850972+00:00
-- url     : https://prove2.me/theorems/7b096ce4-ba76-43c2-98b8-825977e66e52
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0443.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0443_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work3550 : RoundedTauEval :=
  evalTau precision tau3550 contact3550 logTwoBall

theorem center_sq3550 : (center3550.re : ℝ)^2 +
    (center3550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3550 : work3550.theta.ok = true ∧
    work3550.jac.invOK = true ∧ acceptsUnitSq work3550.out = true := by decide +kernel

def cell3550 : CellCertificate where
  tauBall := tau3550
  contactCenter := center3550
  contactBall := contact3550
  work := work3550
  center_sq := center_sq3550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3550.1
  jac_ok := checks3550.2.1
  accepted := checks3550.2.2

def tau3551 : RatBall :=
  ⟨⟨11/640, 51/128⟩, 3/1280⟩
def center3551 : GaussianRat :=
  ⟨3564487/250000000, 73231599/250000000⟩
def contact3551 : RatBall := localContactBall tau3551 center3551
def work3551 : RoundedTauEval :=
  evalTau precision tau3551 contact3551 logTwoBall

theorem center_sq3551 : (center3551.re : ℝ)^2 +
    (center3551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3551 : work3551.theta.ok = true ∧
    work3551.jac.invOK = true ∧ acceptsUnitSq work3551.out = true := by decide +kernel

def cell3551 : CellCertificate where
  tauBall := tau3551
  contactCenter := center3551
  contactBall := contact3551
  work := work3551
  center_sq := center_sq3551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3551.1
  jac_ok := checks3551.2.1
  accepted := checks3551.2.2

def cells : List CellCertificate := [cell3544, cell3545, cell3546, cell3547, cell3548, cell3549, cell3550, cell3551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443


