-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0441
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0441
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:00:37.104376+00:00
-- url     : https://prove2.me/theorems/f4d3d314-01bd-4969-8310-f462512f4c19
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0441.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3528 : RatBall :=
  ⟨⟨1/128, 249/640⟩, 3/1280⟩
def center3528 : GaussianRat :=
  ⟨6423287/1000000000, 285280029/1000000000⟩
def contact3528 : RatBall := localContactBall tau3528 center3528
def work3528 : RoundedTauEval :=
  evalTau precision tau3528 contact3528 logTwoBall

theorem center_sq3528 : (center3528.re : ℝ)^2 +
    (center3528.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3528]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3528 : work3528.theta.ok = true ∧
    work3528.jac.invOK = true ∧ acceptsUnitSq work3528.out = true := by decide +kernel

def cell3528 : CellCertificate where
  tauBall := tau3528
  contactCenter := center3528
  contactBall := contact3528
  work := work3528
  center_sq := center_sq3528
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3528.1
  jac_ok := checks3528.2.1
  accepted := checks3528.2.2

def tau3529 : RatBall :=
  ⟨⟨7/640, 249/640⟩, 3/1280⟩
def center3529 : GaussianRat :=
  ⟨2248057/250000000, 142628517/500000000⟩
def contact3529 : RatBall := localContactBall tau3529 center3529
def work3529 : RoundedTauEval :=
  evalTau precision tau3529 contact3529 logTwoBall

theorem center_sq3529 : (center3529.re : ℝ)^2 +
    (center3529.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3529]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3529 : work3529.theta.ok = true ∧
    work3529.jac.invOK = true ∧ acceptsUnitSq work3529.out = true := by decide +kernel

def cell3529 : CellCertificate where
  tauBall := tau3529
  contactCenter := center3529
  contactBall := contact3529
  work := work3529
  center_sq := center_sq3529
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3529.1
  jac_ok := checks3529.2.1
  accepted := checks3529.2.2

def tau3530 : RatBall :=
  ⟨⟨1/128, 251/640⟩, 3/1280⟩
def center3530 : GaussianRat :=
  ⟨3221293/500000000, 287852971/1000000000⟩
def contact3530 : RatBall := localContactBall tau3530 center3530
def work3530 : RoundedTauEval :=
  evalTau precision tau3530 contact3530 logTwoBall

theorem center_sq3530 : (center3530.re : ℝ)^2 +
    (center3530.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3530]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3530 : work3530.theta.ok = true ∧
    work3530.jac.invOK = true ∧ acceptsUnitSq work3530.out = true := by decide +kernel

def cell3530 : CellCertificate where
  tauBall := tau3530
  contactCenter := center3530
  contactBall := contact3530
  work := work3530
  center_sq := center_sq3530
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3530.1
  jac_ok := checks3530.2.1
  accepted := checks3530.2.2

def tau3531 : RatBall :=
  ⟨⟨7/640, 251/640⟩, 3/1280⟩
def center3531 : GaussianRat :=
  ⟨9019241/1000000000, 287829653/1000000000⟩
def contact3531 : RatBall := localContactBall tau3531 center3531
def work3531 : RoundedTauEval :=
  evalTau precision tau3531 contact3531 logTwoBall

theorem center_sq3531 : (center3531.re : ℝ)^2 +
    (center3531.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3531]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3531 : work3531.theta.ok = true ∧
    work3531.jac.invOK = true ∧ acceptsUnitSq work3531.out = true := by decide +kernel

def cell3531 : CellCertificate where
  tauBall := tau3531
  contactCenter := center3531
  contactBall := contact3531
  work := work3531
  center_sq := center_sq3531
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3531.1
  jac_ok := checks3531.2.1
  accepted := checks3531.2.2

def tau3532 : RatBall :=
  ⟨⟨1/640, 253/640⟩, 3/1280⟩
def center3532 : GaussianRat :=
  ⟨646243/500000000, 72614333/250000000⟩
def contact3532 : RatBall := localContactBall tau3532 center3532
def work3532 : RoundedTauEval :=
  evalTau precision tau3532 contact3532 logTwoBall

theorem center_sq3532 : (center3532.re : ℝ)^2 +
    (center3532.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3532]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3532 : work3532.theta.ok = true ∧
    work3532.jac.invOK = true ∧ acceptsUnitSq work3532.out = true := by decide +kernel

def cell3532 : CellCertificate where
  tauBall := tau3532
  contactCenter := center3532
  contactBall := contact3532
  work := work3532
  center_sq := center_sq3532
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3532.1
  jac_ok := checks3532.2.1
  accepted := checks3532.2.2

def tau3533 : RatBall :=
  ⟨⟨3/640, 253/640⟩, 3/1280⟩
def center3533 : GaussianRat :=
  ⟨3877403/1000000000, 36306181/125000000⟩
def contact3533 : RatBall := localContactBall tau3533 center3533
def work3533 : RoundedTauEval :=
  evalTau precision tau3533 contact3533 logTwoBall

theorem center_sq3533 : (center3533.re : ℝ)^2 +
    (center3533.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3533]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3533 : work3533.theta.ok = true ∧
    work3533.jac.invOK = true ∧ acceptsUnitSq work3533.out = true := by decide +kernel

def cell3533 : CellCertificate where
  tauBall := tau3533
  contactCenter := center3533
  contactBall := contact3533
  work := work3533
  center_sq := center_sq3533
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3533.1
  jac_ok := checks3533.2.1
  accepted := checks3533.2.2

def tau3534 : RatBall :=
  ⟨⟨1/640, 51/128⟩, 3/1280⟩
def center3534 : GaussianRat :=
  ⟨162057/125000000, 58609251/200000000⟩
def contact3534 : RatBall := localContactBall tau3534 center3534
def work3534 : RoundedTauEval :=
  evalTau precision tau3534 contact3534 logTwoBall

theorem center_sq3534 : (center3534.re : ℝ)^2 +
    (center3534.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3534]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3534 : work3534.theta.ok = true ∧
    work3534.jac.invOK = true ∧ acceptsUnitSq work3534.out = true := by decide +kernel

def cell3534 : CellCertificate where
  tauBall := tau3534
  contactCenter := center3534
  contactBall := contact3534
  work := work3534
  center_sq := center_sq3534
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3534.1
  jac_ok := checks3534.2.1
  accepted := checks3534.2.2

def tau3535 : RatBall :=
  ⟨⟨3/640, 51/128⟩, 3/1280⟩
def center3535 : GaussianRat :=
  ⟨3889311/1000000000, 293038261/1000000000⟩
def contact3535 : RatBall := localContactBall tau3535 center3535
def work3535 : RoundedTauEval :=
  evalTau precision tau3535 contact3535 logTwoBall

theorem center_sq3535 : (center3535.re : ℝ)^2 +
    (center3535.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3535]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3535 : work3535.theta.ok = true ∧
    work3535.jac.invOK = true ∧ acceptsUnitSq work3535.out = true := by decide +kernel

def cell3535 : CellCertificate where
  tauBall := tau3535
  contactCenter := center3535
  contactBall := contact3535
  work := work3535
  center_sq := center_sq3535
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3535.1
  jac_ok := checks3535.2.1
  accepted := checks3535.2.2

def cells : List CellCertificate := [cell3528, cell3529, cell3530, cell3531, cell3532, cell3533, cell3534, cell3535]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441

end


