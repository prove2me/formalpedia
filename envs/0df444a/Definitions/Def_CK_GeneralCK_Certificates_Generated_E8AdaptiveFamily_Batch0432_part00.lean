-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0432_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:12:03.543806+00:00
-- url     : https://prove2.me/theorems/f7fe5bd4-228e-4254-be3d-2709791144ae
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0432 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3456 : RatBall :=
  ⟨⟨-23/640, 49/128⟩, 3/1280⟩
def center3456 : GaussianRat :=
  ⟨-7337051/250000000, 279688291/1000000000⟩
def contact3456 : RatBall := localContactBall tau3456 center3456
def work3456 : RoundedTauEval :=
  evalTau precision tau3456 contact3456 logTwoBall

theorem center_sq3456 : (center3456.re : ℝ)^2 +
    (center3456.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3456]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3456 : work3456.theta.ok = true ∧
    work3456.jac.invOK = true ∧ acceptsUnitSq work3456.out = true := by decide +kernel

def cell3456 : CellCertificate where
  tauBall := tau3456
  contactCenter := center3456
  contactBall := contact3456
  work := work3456
  center_sq := center_sq3456
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3456.1
  jac_ok := checks3456.2.1
  accepted := checks3456.2.2

def tau3457 : RatBall :=
  ⟨⟨-21/640, 49/128⟩, 3/1280⟩
def center3457 : GaussianRat :=
  ⟨-6700043/250000000, 139884999/500000000⟩
def contact3457 : RatBall := localContactBall tau3457 center3457
def work3457 : RoundedTauEval :=
  evalTau precision tau3457 contact3457 logTwoBall

theorem center_sq3457 : (center3457.re : ℝ)^2 +
    (center3457.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3457]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3457 : work3457.theta.ok = true ∧
    work3457.jac.invOK = true ∧ acceptsUnitSq work3457.out = true := by decide +kernel

def cell3457 : CellCertificate where
  tauBall := tau3457
  contactCenter := center3457
  contactBall := contact3457
  work := work3457
  center_sq := center_sq3457
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3457.1
  jac_ok := checks3457.2.1
  accepted := checks3457.2.2

def tau3458 : RatBall :=
  ⟨⟨-23/640, 247/640⟩, 3/1280⟩
def center3458 : GaussianRat :=
  ⟨-1839637/62500000, 141119723/500000000⟩
def contact3458 : RatBall := localContactBall tau3458 center3458
def work3458 : RoundedTauEval :=
  evalTau precision tau3458 contact3458 logTwoBall

theorem center_sq3458 : (center3458.re : ℝ)^2 +
    (center3458.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3458]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3458 : work3458.theta.ok = true ∧
    work3458.jac.invOK = true ∧ acceptsUnitSq work3458.out = true := by decide +kernel

def cell3458 : CellCertificate where
  tauBall := tau3458
  contactCenter := center3458
  contactBall := contact3458
  work := work3458
  center_sq := center_sq3458
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3458.1
  jac_ok := checks3458.2.1
  accepted := checks3458.2.2

def tau3459 : RatBall :=
  ⟨⟨-21/640, 247/640⟩, 3/1280⟩
def center3459 : GaussianRat :=
  ⟨-26878737/1000000000, 282322297/1000000000⟩
def contact3459 : RatBall := localContactBall tau3459 center3459
def work3459 : RoundedTauEval :=
  evalTau precision tau3459 contact3459 logTwoBall

theorem center_sq3459 : (center3459.re : ℝ)^2 +
    (center3459.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3459]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3459 : work3459.theta.ok = true ∧
    work3459.jac.invOK = true ∧ acceptsUnitSq work3459.out = true := by decide +kernel

def cell3459 : CellCertificate where
  tauBall := tau3459
  contactCenter := center3459
  contactBall := contact3459
  work := work3459
  center_sq := center_sq3459
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3459.1
  jac_ok := checks3459.2.1
  accepted := checks3459.2.2

def tau3460 : RatBall :=
  ⟨⟨-31/640, 249/640⟩, 3/1280⟩
def center3460 : GaussianRat :=
  ⟨-19880031/500000000, 56877303/200000000⟩
def contact3460 : RatBall := localContactBall tau3460 center3460
def work3460 : RoundedTauEval :=
  evalTau precision tau3460 contact3460 logTwoBall

theorem center_sq3460 : (center3460.re : ℝ)^2 +
    (center3460.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3460]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3460 : work3460.theta.ok = true ∧
    work3460.jac.invOK = true ∧ acceptsUnitSq work3460.out = true := by decide +kernel

def cell3460 : CellCertificate where
  tauBall := tau3460
  contactCenter := center3460
  contactBall := contact3460
  work := work3460
  center_sq := center_sq3460
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3460.1
  jac_ok := checks3460.2.1
  accepted := checks3460.2.2

def tau3461 : RatBall :=
  ⟨⟨-29/640, 249/640⟩, 3/1280⟩
def center3461 : GaussianRat :=
  ⟨-37202587/1000000000, 284500691/1000000000⟩
def contact3461 : RatBall := localContactBall tau3461 center3461
def work3461 : RoundedTauEval :=
  evalTau precision tau3461 contact3461 logTwoBall

theorem center_sq3461 : (center3461.re : ℝ)^2 +
    (center3461.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3461]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3461 : work3461.theta.ok = true ∧
    work3461.jac.invOK = true ∧ acceptsUnitSq work3461.out = true := by decide +kernel

def cell3461 : CellCertificate where
  tauBall := tau3461
  contactCenter := center3461
  contactBall := contact3461
  work := work3461
  center_sq := center_sq3461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3461.1
  jac_ok := checks3461.2.1
  accepted := checks3461.2.2

def tau3462 : RatBall :=
  ⟨⟨-31/640, 251/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432


