-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0454_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:41:14.557316+00:00
-- url     : https://prove2.me/theorems/3c864e07-0e26-42df-aae4-71285ba56f20
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0454 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3632 : RatBall :=
  ⟨⟨41/640, 249/640⟩, 3/1280⟩
def center3632 : GaussianRat :=
  ⟨13130217/250000000, 283703773/1000000000⟩
def contact3632 : RatBall := localContactBall tau3632 center3632
def work3632 : RoundedTauEval :=
  evalTau precision tau3632 contact3632 logTwoBall

theorem center_sq3632 : (center3632.re : ℝ)^2 +
    (center3632.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3632]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3632 : work3632.theta.ok = true ∧
    work3632.jac.invOK = true ∧ acceptsUnitSq work3632.out = true := by decide +kernel

def cell3632 : CellCertificate where
  tauBall := tau3632
  contactCenter := center3632
  contactBall := contact3632
  work := work3632
  center_sq := center_sq3632
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3632.1
  jac_ok := checks3632.2.1
  accepted := checks3632.2.2

def tau3633 : RatBall :=
  ⟨⟨43/640, 249/640⟩, 3/1280⟩
def center3633 : GaussianRat :=
  ⟨13766751/250000000, 141772517/500000000⟩
def contact3633 : RatBall := localContactBall tau3633 center3633
def work3633 : RoundedTauEval :=
  evalTau precision tau3633 contact3633 logTwoBall

theorem center_sq3633 : (center3633.re : ℝ)^2 +
    (center3633.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3633]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3633 : work3633.theta.ok = true ∧
    work3633.jac.invOK = true ∧ acceptsUnitSq work3633.out = true := by decide +kernel

def cell3633 : CellCertificate where
  tauBall := tau3633
  contactCenter := center3633
  contactBall := contact3633
  work := work3633
  center_sq := center_sq3633
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3633.1
  jac_ok := checks3633.2.1
  accepted := checks3633.2.2

def tau3634 : RatBall :=
  ⟨⟨41/640, 251/640⟩, 3/1280⟩
def center3634 : GaussianRat :=
  ⟨52677009/1000000000, 143127347/500000000⟩
def contact3634 : RatBall := localContactBall tau3634 center3634
def work3634 : RoundedTauEval :=
  evalTau precision tau3634 contact3634 logTwoBall

theorem center_sq3634 : (center3634.re : ℝ)^2 +
    (center3634.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3634]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3634 : work3634.theta.ok = true ∧
    work3634.jac.invOK = true ∧ acceptsUnitSq work3634.out = true := by decide +kernel

def cell3634 : CellCertificate where
  tauBall := tau3634
  contactCenter := center3634
  contactBall := contact3634
  work := work3634
  center_sq := center_sq3634
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3634.1
  jac_ok := checks3634.2.1
  accepted := checks3634.2.2

def tau3635 : RatBall :=
  ⟨⟨43/640, 251/640⟩, 3/1280⟩
def center3635 : GaussianRat :=
  ⟨2761527/50000000, 286093747/1000000000⟩
def contact3635 : RatBall := localContactBall tau3635 center3635
def work3635 : RoundedTauEval :=
  evalTau precision tau3635 contact3635 logTwoBall

theorem center_sq3635 : (center3635.re : ℝ)^2 +
    (center3635.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3635]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3635 : work3635.theta.ok = true ∧
    work3635.jac.invOK = true ∧ acceptsUnitSq work3635.out = true := by decide +kernel

def cell3635 : CellCertificate where
  tauBall := tau3635
  contactCenter := center3635
  contactBall := contact3635
  work := work3635
  center_sq := center_sq3635
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3635.1
  jac_ok := checks3635.2.1
  accepted := checks3635.2.2

def tau3636 : RatBall :=
  ⟨⟨9/128, 249/640⟩, 3/1280⟩
def center3636 : GaussianRat :=
  ⟨28805449/500000000, 141689483/500000000⟩
def contact3636 : RatBall := localContactBall tau3636 center3636
def work3636 : RoundedTauEval :=
  evalTau precision tau3636 contact3636 logTwoBall

theorem center_sq3636 : (center3636.re : ℝ)^2 +
    (center3636.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3636]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3636 : work3636.theta.ok = true ∧
    work3636.jac.invOK = true ∧ acceptsUnitSq work3636.out = true := by decide +kernel

def cell3636 : CellCertificate where
  tauBall := tau3636
  contactCenter := center3636
  contactBall := contact3636
  work := work3636
  center_sq := center_sq3636
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3636.1
  jac_ok := checks3636.2.1
  accepted := checks3636.2.2

def tau3637 : RatBall :=
  ⟨⟨47/640, 249/640⟩, 3/1280⟩
def center3637 : GaussianRat :=
  ⟨60152449/1000000000, 283205599/1000000000⟩
def contact3637 : RatBall := localContactBall tau3637 center3637
def work3637 : RoundedTauEval :=
  evalTau precision tau3637 contact3637 logTwoBall

theorem center_sq3637 : (center3637.re : ℝ)^2 +
    (center3637.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3637]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3637 : work3637.theta.ok = true ∧
    work3637.jac.invOK = true ∧ acceptsUnitSq work3637.out = true := by decide +kernel

def cell3637 : CellCertificate where
  tauBall := tau3637
  contactCenter := center3637
  contactBall := contact3637
  work := work3637
  center_sq := center_sq3637
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3637.1
  jac_ok := checks3637.2.1
  accepted := checks3637.2.2

def tau3638 : RatBall :=
  ⟨⟨9/128, 251/640⟩, 3/1280⟩
def center3638 : GaussianRat :=
  ⟨57781797/1000000000, 285925371/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454


