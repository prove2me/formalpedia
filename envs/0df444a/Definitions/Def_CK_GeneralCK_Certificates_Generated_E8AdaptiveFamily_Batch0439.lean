-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:33:04.629296+00:00
-- url     : https://prove2.me/theorems/d9e5e28a-b5c8-4258-a0a6-ccb86e89ad6c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0439.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0439_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3518 : RatBall :=
  ⟨⟨-7/640, 51/128⟩, 3/1280⟩
def center3518 : GaussianRat :=
  ⟨-9074409/1000000000, 292998297/1000000000⟩
def contact3518 : RatBall := localContactBall tau3518 center3518
def work3518 : RoundedTauEval :=
  evalTau precision tau3518 contact3518 logTwoBall

theorem center_sq3518 : (center3518.re : ℝ)^2 +
    (center3518.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3518]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3518 : work3518.theta.ok = true ∧
    work3518.jac.invOK = true ∧ acceptsUnitSq work3518.out = true := by decide +kernel

def cell3518 : CellCertificate where
  tauBall := tau3518
  contactCenter := center3518
  contactBall := contact3518
  work := work3518
  center_sq := center_sq3518
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3518.1
  jac_ok := checks3518.2.1
  accepted := checks3518.2.2

def tau3519 : RatBall :=
  ⟨⟨-1/128, 51/128⟩, 3/1280⟩
def center3519 : GaussianRat :=
  ⟨-6481999/1000000000, 146511137/500000000⟩
def contact3519 : RatBall := localContactBall tau3519 center3519
def work3519 : RoundedTauEval :=
  evalTau precision tau3519 contact3519 logTwoBall

theorem center_sq3519 : (center3519.re : ℝ)^2 +
    (center3519.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3519]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3519 : work3519.theta.ok = true ∧
    work3519.jac.invOK = true ∧ acceptsUnitSq work3519.out = true := by decide +kernel

def cell3519 : CellCertificate where
  tauBall := tau3519
  contactCenter := center3519
  contactBall := contact3519
  work := work3519
  center_sq := center_sq3519
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3519.1
  jac_ok := checks3519.2.1
  accepted := checks3519.2.2

def cells : List CellCertificate := [cell3512, cell3513, cell3514, cell3515, cell3516, cell3517, cell3518, cell3519]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439


