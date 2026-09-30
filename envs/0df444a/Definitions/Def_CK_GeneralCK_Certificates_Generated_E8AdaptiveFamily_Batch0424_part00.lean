-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0424_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:37:52.851099+00:00
-- url     : https://prove2.me/theorems/f554df30-4262-47ad-94e6-2d6a1458f465
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0424 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3392 : RatBall :=
  ⟨⟨-49/640, 247/640⟩, 3/1280⟩
def center3392 : GaussianRat :=
  ⟨-6250857/100000000, 280490707/1000000000⟩
def contact3392 : RatBall := localContactBall tau3392 center3392
def work3392 : RoundedTauEval :=
  evalTau precision tau3392 contact3392 logTwoBall

theorem center_sq3392 : (center3392.re : ℝ)^2 +
    (center3392.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3392]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3392 : work3392.theta.ok = true ∧
    work3392.jac.invOK = true ∧ acceptsUnitSq work3392.out = true := by decide +kernel

def cell3392 : CellCertificate where
  tauBall := tau3392
  contactCenter := center3392
  contactBall := contact3392
  work := work3392
  center_sq := center_sq3392
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3392.1
  jac_ok := checks3392.2.1
  accepted := checks3392.2.2

def tau3393 : RatBall :=
  ⟨⟨-63/640, 249/640⟩, 3/1280⟩
def center3393 : GaussianRat :=
  ⟨-16077783/200000000, 281560103/1000000000⟩
def contact3393 : RatBall := localContactBall tau3393 center3393
def work3393 : RoundedTauEval :=
  evalTau precision tau3393 contact3393 logTwoBall

theorem center_sq3393 : (center3393.re : ℝ)^2 +
    (center3393.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3393]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3393 : work3393.theta.ok = true ∧
    work3393.jac.invOK = true ∧ acceptsUnitSq work3393.out = true := by decide +kernel

def cell3393 : CellCertificate where
  tauBall := tau3393
  contactCenter := center3393
  contactBall := contact3393
  work := work3393
  center_sq := center_sq3393
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3393.1
  jac_ok := checks3393.2.1
  accepted := checks3393.2.2

def tau3394 : RatBall :=
  ⟨⟨-61/640, 249/640⟩, 3/1280⟩
def center3394 : GaussianRat :=
  ⟨-38934787/500000000, 281790577/1000000000⟩
def contact3394 : RatBall := localContactBall tau3394 center3394
def work3394 : RoundedTauEval :=
  evalTau precision tau3394 contact3394 logTwoBall

theorem center_sq3394 : (center3394.re : ℝ)^2 +
    (center3394.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3394]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3394 : work3394.theta.ok = true ∧
    work3394.jac.invOK = true ∧ acceptsUnitSq work3394.out = true := by decide +kernel

def cell3394 : CellCertificate where
  tauBall := tau3394
  contactCenter := center3394
  contactBall := contact3394
  work := work3394
  center_sq := center_sq3394
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3394.1
  jac_ok := checks3394.2.1
  accepted := checks3394.2.2

def tau3395 : RatBall :=
  ⟨⟨-59/640, 249/640⟩, 3/1280⟩
def center3395 : GaussianRat :=
  ⟨-75347127/1000000000, 8812939/31250000⟩
def contact3395 : RatBall := localContactBall tau3395 center3395
def work3395 : RoundedTauEval :=
  evalTau precision tau3395 contact3395 logTwoBall

theorem center_sq3395 : (center3395.re : ℝ)^2 +
    (center3395.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3395]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3395 : work3395.theta.ok = true ∧
    work3395.jac.invOK = true ∧ acceptsUnitSq work3395.out = true := by decide +kernel

def cell3395 : CellCertificate where
  tauBall := tau3395
  contactCenter := center3395
  contactBall := contact3395
  work := work3395
  center_sq := center_sq3395
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3395.1
  jac_ok := checks3395.2.1
  accepted := checks3395.2.2

def tau3396 : RatBall :=
  ⟨⟨-57/640, 249/640⟩, 3/1280⟩
def center3396 : GaussianRat :=
  ⟨-14564333/200000000, 70557619/250000000⟩
def contact3396 : RatBall := localContactBall tau3396 center3396
def work3396 : RoundedTauEval :=
  evalTau precision tau3396 contact3396 logTwoBall

theorem center_sq3396 : (center3396.re : ℝ)^2 +
    (center3396.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3396]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3396 : work3396.theta.ok = true ∧
    work3396.jac.invOK = true ∧ acceptsUnitSq work3396.out = true := by decide +kernel

def cell3396 : CellCertificate where
  tauBall := tau3396
  contactCenter := center3396
  contactBall := contact3396
  work := work3396
  center_sq := center_sq3396
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3396.1
  jac_ok := checks3396.2.1
  accepted := checks3396.2.2

def tau3397 : RatBall :=
  ⟨⟨-11/128, 249/640⟩, 3/1280⟩
def center3397 : GaussianRat :=
  ⟨-70293283/1000000000, 14121991/50000000⟩
def contact3397 : RatBall := localContactBall tau3397 center3397
def work3397 : RoundedTauEval :=
  evalTau precision tau3397 contact3397 logTwoBall

theorem center_sq3397 : (center3397.re : ℝ)^2 +
    (center3397.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3397]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3397 : work3397.theta.ok = true ∧
    work3397.jac.invOK = true ∧ acceptsUnitSq work3397.out = true := by decide +kernel

def cell3397 : CellCertificate where
  tauBall := tau3397
  contactCenter := center3397
  contactBall := contact3397
  work := work3397
  center_sq := center_sq3397
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3397.1
  jac_ok := checks3397.2.1
  accepted := checks3397.2.2

def tau3398 : RatBall :=
  ⟨⟨-53/640, 249/640⟩, 3/1280⟩
def center3398 : GaussianRat :=
  ⟨-33881037/500000000, 282642041/1000000000⟩
def contact3398 : RatBall := localContactBall tau3398 center3398
def work3398 : RoundedTauEval :=
  evalTau precision tau3398 contact3398 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424


