-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:58:32.38726+00:00
-- url     : https://prove2.me/theorems/bfac37de-a818-468b-8fb0-e4d6b62878c3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0448 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0448_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3587 : work3587.theta.ok = true ∧
    work3587.jac.invOK = true ∧ acceptsUnitSq work3587.out = true := by decide +kernel

def cell3587 : CellCertificate where
  tauBall := tau3587
  contactCenter := center3587
  contactBall := contact3587
  work := work3587
  center_sq := center_sq3587
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3587.1
  jac_ok := checks3587.2.1
  accepted := checks3587.2.2

def tau3588 : RatBall :=
  ⟨⟨29/640, 249/640⟩, 3/1280⟩
def center3588 : GaussianRat :=
  ⟨37202587/1000000000, 284500691/1000000000⟩
def contact3588 : RatBall := localContactBall tau3588 center3588
def work3588 : RoundedTauEval :=
  evalTau precision tau3588 contact3588 logTwoBall

theorem center_sq3588 : (center3588.re : ℝ)^2 +
    (center3588.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3588]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3588 : work3588.theta.ok = true ∧
    work3588.jac.invOK = true ∧ acceptsUnitSq work3588.out = true := by decide +kernel

def cell3588 : CellCertificate where
  tauBall := tau3588
  contactCenter := center3588
  contactBall := contact3588
  work := work3588
  center_sq := center_sq3588
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3588.1
  jac_ok := checks3588.2.1
  accepted := checks3588.2.2

def tau3589 : RatBall :=
  ⟨⟨31/640, 249/640⟩, 3/1280⟩
def center3589 : GaussianRat :=
  ⟨19880031/500000000, 56877303/200000000⟩
def contact3589 : RatBall := localContactBall tau3589 center3589
def work3589 : RoundedTauEval :=
  evalTau precision tau3589 contact3589 logTwoBall

theorem center_sq3589 : (center3589.re : ℝ)^2 +
    (center3589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3589 : work3589.theta.ok = true ∧
    work3589.jac.invOK = true ∧ acceptsUnitSq work3589.out = true := by decide +kernel

def cell3589 : CellCertificate where
  tauBall := tau3589
  contactCenter := center3589
  contactBall := contact3589
  work := work3589
  center_sq := center_sq3589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3589.1
  jac_ok := checks3589.2.1
  accepted := checks3589.2.2

def tau3590 : RatBall :=
  ⟨⟨29/640, 251/640⟩, 3/1280⟩
def center3590 : GaussianRat :=
  ⟨1865689/50000000, 287062723/1000000000⟩
def contact3590 : RatBall := localContactBall tau3590 center3590
def work3590 : RoundedTauEval :=
  evalTau precision tau3590 contact3590 logTwoBall

theorem center_sq3590 : (center3590.re : ℝ)^2 +
    (center3590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3590 : work3590.theta.ok = true ∧
    work3590.jac.invOK = true ∧ acceptsUnitSq work3590.out = true := by decide +kernel

def cell3590 : CellCertificate where
  tauBall := tau3590
  contactCenter := center3590
  contactBall := contact3590
  work := work3590
  center_sq := center_sq3590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3590.1
  jac_ok := checks3590.2.1
  accepted := checks3590.2.2

def tau3591 : RatBall :=
  ⟨⟨31/640, 251/640⟩, 3/1280⟩
def center3591 : GaussianRat :=
  ⟨4984851/125000000, 286946953/1000000000⟩
def contact3591 : RatBall := localContactBall tau3591 center3591

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448


