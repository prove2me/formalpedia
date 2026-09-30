-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0440_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:06.275705+00:00
-- url     : https://prove2.me/theorems/7e0c3b14-52f6-422f-b700-b42ff287088d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0440 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3520 : RatBall :=
  ⟨⟨-3/640, 253/640⟩, 3/1280⟩
def center3520 : GaussianRat :=
  ⟨-3877403/1000000000, 36306181/125000000⟩
def contact3520 : RatBall := localContactBall tau3520 center3520
def work3520 : RoundedTauEval :=
  evalTau precision tau3520 contact3520 logTwoBall

theorem center_sq3520 : (center3520.re : ℝ)^2 +
    (center3520.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3520]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3520 : work3520.theta.ok = true ∧
    work3520.jac.invOK = true ∧ acceptsUnitSq work3520.out = true := by decide +kernel

def cell3520 : CellCertificate where
  tauBall := tau3520
  contactCenter := center3520
  contactBall := contact3520
  work := work3520
  center_sq := center_sq3520
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3520.1
  jac_ok := checks3520.2.1
  accepted := checks3520.2.2

def tau3521 : RatBall :=
  ⟨⟨-1/640, 253/640⟩, 3/1280⟩
def center3521 : GaussianRat :=
  ⟨-646243/500000000, 72614333/250000000⟩
def contact3521 : RatBall := localContactBall tau3521 center3521
def work3521 : RoundedTauEval :=
  evalTau precision tau3521 contact3521 logTwoBall

theorem center_sq3521 : (center3521.re : ℝ)^2 +
    (center3521.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3521]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3521 : work3521.theta.ok = true ∧
    work3521.jac.invOK = true ∧ acceptsUnitSq work3521.out = true := by decide +kernel

def cell3521 : CellCertificate where
  tauBall := tau3521
  contactCenter := center3521
  contactBall := contact3521
  work := work3521
  center_sq := center_sq3521
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3521.1
  jac_ok := checks3521.2.1
  accepted := checks3521.2.2

def tau3522 : RatBall :=
  ⟨⟨-3/640, 51/128⟩, 3/1280⟩
def center3522 : GaussianRat :=
  ⟨-3889311/1000000000, 293038261/1000000000⟩
def contact3522 : RatBall := localContactBall tau3522 center3522
def work3522 : RoundedTauEval :=
  evalTau precision tau3522 contact3522 logTwoBall

theorem center_sq3522 : (center3522.re : ℝ)^2 +
    (center3522.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3522]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3522 : work3522.theta.ok = true ∧
    work3522.jac.invOK = true ∧ acceptsUnitSq work3522.out = true := by decide +kernel

def cell3522 : CellCertificate where
  tauBall := tau3522
  contactCenter := center3522
  contactBall := contact3522
  work := work3522
  center_sq := center_sq3522
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3522.1
  jac_ok := checks3522.2.1
  accepted := checks3522.2.2

def tau3523 : RatBall :=
  ⟨⟨-1/640, 51/128⟩, 3/1280⟩
def center3523 : GaussianRat :=
  ⟨-162057/125000000, 58609251/200000000⟩
def contact3523 : RatBall := localContactBall tau3523 center3523
def work3523 : RoundedTauEval :=
  evalTau precision tau3523 contact3523 logTwoBall

theorem center_sq3523 : (center3523.re : ℝ)^2 +
    (center3523.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3523 : work3523.theta.ok = true ∧
    work3523.jac.invOK = true ∧ acceptsUnitSq work3523.out = true := by decide +kernel

def cell3523 : CellCertificate where
  tauBall := tau3523
  contactCenter := center3523
  contactBall := contact3523
  work := work3523
  center_sq := center_sq3523
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3523.1
  jac_ok := checks3523.2.1
  accepted := checks3523.2.2

def tau3524 : RatBall :=
  ⟨⟨1/640, 249/640⟩, 3/1280⟩
def center3524 : GaussianRat :=
  ⟨1284711/1000000000, 285303029/1000000000⟩
def contact3524 : RatBall := localContactBall tau3524 center3524
def work3524 : RoundedTauEval :=
  evalTau precision tau3524 contact3524 logTwoBall

theorem center_sq3524 : (center3524.re : ℝ)^2 +
    (center3524.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3524]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3524 : work3524.theta.ok = true ∧
    work3524.jac.invOK = true ∧ acceptsUnitSq work3524.out = true := by decide +kernel

def cell3524 : CellCertificate where
  tauBall := tau3524
  contactCenter := center3524
  contactBall := contact3524
  work := work3524
  center_sq := center_sq3524
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3524.1
  jac_ok := checks3524.2.1
  accepted := checks3524.2.2

def tau3525 : RatBall :=
  ⟨⟨3/640, 249/640⟩, 3/1280⟩
def center3525 : GaussianRat :=
  ⟨3854079/1000000000, 142647681/500000000⟩
def contact3525 : RatBall := localContactBall tau3525 center3525
def work3525 : RoundedTauEval :=
  evalTau precision tau3525 contact3525 logTwoBall

theorem center_sq3525 : (center3525.re : ℝ)^2 +
    (center3525.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3525]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3525 : work3525.theta.ok = true ∧
    work3525.jac.invOK = true ∧ acceptsUnitSq work3525.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440


