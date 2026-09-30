-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0442
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0442
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:58:53.881408+00:00
-- url     : https://prove2.me/theorems/55d6be05-6c27-4d2e-895d-b0fdc18aaf1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0442.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3536 : RatBall :=
  ⟨⟨1/128, 253/640⟩, 3/1280⟩
def center3536 : GaussianRat :=
  ⟨1292431/200000000, 290433683/1000000000⟩
def contact3536 : RatBall := localContactBall tau3536 center3536
def work3536 : RoundedTauEval :=
  evalTau precision tau3536 contact3536 logTwoBall

theorem center_sq3536 : (center3536.re : ℝ)^2 +
    (center3536.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3536]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3536 : work3536.theta.ok = true ∧
    work3536.jac.invOK = true ∧ acceptsUnitSq work3536.out = true := by decide +kernel

def cell3536 : CellCertificate where
  tauBall := tau3536
  contactCenter := center3536
  contactBall := contact3536
  work := work3536
  center_sq := center_sq3536
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3536.1
  jac_ok := checks3536.2.1
  accepted := checks3536.2.2

def tau3537 : RatBall :=
  ⟨⟨7/640, 253/640⟩, 3/1280⟩
def center3537 : GaussianRat :=
  ⟨9046633/1000000000, 145205019/500000000⟩
def contact3537 : RatBall := localContactBall tau3537 center3537
def work3537 : RoundedTauEval :=
  evalTau precision tau3537 contact3537 logTwoBall

theorem center_sq3537 : (center3537.re : ℝ)^2 +
    (center3537.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3537]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3537 : work3537.theta.ok = true ∧
    work3537.jac.invOK = true ∧ acceptsUnitSq work3537.out = true := by decide +kernel

def cell3537 : CellCertificate where
  tauBall := tau3537
  contactCenter := center3537
  contactBall := contact3537
  work := work3537
  center_sq := center_sq3537
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3537.1
  jac_ok := checks3537.2.1
  accepted := checks3537.2.2

def tau3538 : RatBall :=
  ⟨⟨1/128, 51/128⟩, 3/1280⟩
def center3538 : GaussianRat :=
  ⟨6481999/1000000000, 146511137/500000000⟩
def contact3538 : RatBall := localContactBall tau3538 center3538
def work3538 : RoundedTauEval :=
  evalTau precision tau3538 contact3538 logTwoBall

theorem center_sq3538 : (center3538.re : ℝ)^2 +
    (center3538.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3538]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3538 : work3538.theta.ok = true ∧
    work3538.jac.invOK = true ∧ acceptsUnitSq work3538.out = true := by decide +kernel

def cell3538 : CellCertificate where
  tauBall := tau3538
  contactCenter := center3538
  contactBall := contact3538
  work := work3538
  center_sq := center_sq3538
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3538.1
  jac_ok := checks3538.2.1
  accepted := checks3538.2.2

def tau3539 : RatBall :=
  ⟨⟨7/640, 51/128⟩, 3/1280⟩
def center3539 : GaussianRat :=
  ⟨9074409/1000000000, 292998297/1000000000⟩
def contact3539 : RatBall := localContactBall tau3539 center3539
def work3539 : RoundedTauEval :=
  evalTau precision tau3539 contact3539 logTwoBall

theorem center_sq3539 : (center3539.re : ℝ)^2 +
    (center3539.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3539]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3539 : work3539.theta.ok = true ∧
    work3539.jac.invOK = true ∧ acceptsUnitSq work3539.out = true := by decide +kernel

def cell3539 : CellCertificate where
  tauBall := tau3539
  contactCenter := center3539
  contactBall := contact3539
  work := work3539
  center_sq := center_sq3539
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3539.1
  jac_ok := checks3539.2.1
  accepted := checks3539.2.2

def tau3540 : RatBall :=
  ⟨⟨9/640, 249/640⟩, 3/1280⟩
def center3540 : GaussianRat :=
  ⟨2890199/250000000, 14261319/50000000⟩
def contact3540 : RatBall := localContactBall tau3540 center3540
def work3540 : RoundedTauEval :=
  evalTau precision tau3540 contact3540 logTwoBall

theorem center_sq3540 : (center3540.re : ℝ)^2 +
    (center3540.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3540]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3540 : work3540.theta.ok = true ∧
    work3540.jac.invOK = true ∧ acceptsUnitSq work3540.out = true := by decide +kernel

def cell3540 : CellCertificate where
  tauBall := tau3540
  contactCenter := center3540
  contactBall := contact3540
  work := work3540
  center_sq := center_sq3540
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3540.1
  jac_ok := checks3540.2.1
  accepted := checks3540.2.2

def tau3541 : RatBall :=
  ⟨⟨11/640, 249/640⟩, 3/1280⟩
def center3541 : GaussianRat :=
  ⟨14128883/1000000000, 11407523/40000000⟩
def contact3541 : RatBall := localContactBall tau3541 center3541
def work3541 : RoundedTauEval :=
  evalTau precision tau3541 contact3541 logTwoBall

theorem center_sq3541 : (center3541.re : ℝ)^2 +
    (center3541.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3541]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3541 : work3541.theta.ok = true ∧
    work3541.jac.invOK = true ∧ acceptsUnitSq work3541.out = true := by decide +kernel

def cell3541 : CellCertificate where
  tauBall := tau3541
  contactCenter := center3541
  contactBall := contact3541
  work := work3541
  center_sq := center_sq3541
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3541.1
  jac_ok := checks3541.2.1
  accepted := checks3541.2.2

def tau3542 : RatBall :=
  ⟨⟨9/640, 251/640⟩, 3/1280⟩
def center3542 : GaussianRat :=
  ⟨5797759/500000000, 28779857/100000000⟩
def contact3542 : RatBall := localContactBall tau3542 center3542
def work3542 : RoundedTauEval :=
  evalTau precision tau3542 contact3542 logTwoBall

theorem center_sq3542 : (center3542.re : ℝ)^2 +
    (center3542.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3542]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3542 : work3542.theta.ok = true ∧
    work3542.jac.invOK = true ∧ acceptsUnitSq work3542.out = true := by decide +kernel

def cell3542 : CellCertificate where
  tauBall := tau3542
  contactCenter := center3542
  contactBall := contact3542
  work := work3542
  center_sq := center_sq3542
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3542.1
  jac_ok := checks3542.2.1
  accepted := checks3542.2.2

def tau3543 : RatBall :=
  ⟨⟨11/640, 251/640⟩, 3/1280⟩
def center3543 : GaussianRat :=
  ⟨14171307/1000000000, 287759727/1000000000⟩
def contact3543 : RatBall := localContactBall tau3543 center3543
def work3543 : RoundedTauEval :=
  evalTau precision tau3543 contact3543 logTwoBall

theorem center_sq3543 : (center3543.re : ℝ)^2 +
    (center3543.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3543]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3543 : work3543.theta.ok = true ∧
    work3543.jac.invOK = true ∧ acceptsUnitSq work3543.out = true := by decide +kernel

def cell3543 : CellCertificate where
  tauBall := tau3543
  contactCenter := center3543
  contactBall := contact3543
  work := work3543
  center_sq := center_sq3543
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3543.1
  jac_ok := checks3543.2.1
  accepted := checks3543.2.2

def cells : List CellCertificate := [cell3536, cell3537, cell3538, cell3539, cell3540, cell3541, cell3542, cell3543]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442

end


