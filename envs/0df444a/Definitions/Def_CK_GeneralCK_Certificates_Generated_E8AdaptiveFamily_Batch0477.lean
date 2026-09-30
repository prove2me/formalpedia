-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0477
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0477
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:53.595599+00:00
-- url     : https://prove2.me/theorems/aa31363d-2fd4-415b-a4f1-fef0bfc1bf55
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0477.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3816 : RatBall :=
  ⟨⟨113/640, 227/640⟩, 3/1280⟩
def center3816 : GaussianRat :=
  ⟨138097011/1000000000, 61864659/250000000⟩
def contact3816 : RatBall := localContactBall tau3816 center3816
def work3816 : RoundedTauEval :=
  evalTau precision tau3816 contact3816 logTwoBall

theorem center_sq3816 : (center3816.re : ℝ)^2 +
    (center3816.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3816]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3816 : work3816.theta.ok = true ∧
    work3816.jac.invOK = true ∧ acceptsUnitSq work3816.out = true := by decide +kernel

def cell3816 : CellCertificate where
  tauBall := tau3816
  contactCenter := center3816
  contactBall := contact3816
  work := work3816
  center_sq := center_sq3816
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3816.1
  jac_ok := checks3816.2.1
  accepted := checks3816.2.2

def tau3817 : RatBall :=
  ⟨⟨23/128, 227/640⟩, 3/1280⟩
def center3817 : GaussianRat :=
  ⟨140448677/1000000000, 247117293/1000000000⟩
def contact3817 : RatBall := localContactBall tau3817 center3817
def work3817 : RoundedTauEval :=
  evalTau precision tau3817 contact3817 logTwoBall

theorem center_sq3817 : (center3817.re : ℝ)^2 +
    (center3817.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3817]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3817 : work3817.theta.ok = true ∧
    work3817.jac.invOK = true ∧ acceptsUnitSq work3817.out = true := by decide +kernel

def cell3817 : CellCertificate where
  tauBall := tau3817
  contactCenter := center3817
  contactBall := contact3817
  work := work3817
  center_sq := center_sq3817
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3817.1
  jac_ok := checks3817.2.1
  accepted := checks3817.2.2

def tau3818 : RatBall :=
  ⟨⟨117/640, 45/128⟩, 3/1280⟩
def center3818 : GaussianRat :=
  ⟨8903089/62500000, 244428717/1000000000⟩
def contact3818 : RatBall := localContactBall tau3818 center3818
def work3818 : RoundedTauEval :=
  evalTau precision tau3818 contact3818 logTwoBall

theorem center_sq3818 : (center3818.re : ℝ)^2 +
    (center3818.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3818]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3818 : work3818.theta.ok = true ∧
    work3818.jac.invOK = true ∧ acceptsUnitSq work3818.out = true := by decide +kernel

def cell3818 : CellCertificate where
  tauBall := tau3818
  contactCenter := center3818
  contactBall := contact3818
  work := work3818
  center_sq := center_sq3818
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3818.1
  jac_ok := checks3818.2.1
  accepted := checks3818.2.2

def tau3819 : RatBall :=
  ⟨⟨119/640, 45/128⟩, 3/1280⟩
def center3819 : GaussianRat :=
  ⟨72393537/500000000, 122041161/500000000⟩
def contact3819 : RatBall := localContactBall tau3819 center3819
def work3819 : RoundedTauEval :=
  evalTau precision tau3819 contact3819 logTwoBall

theorem center_sq3819 : (center3819.re : ℝ)^2 +
    (center3819.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3819]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3819 : work3819.theta.ok = true ∧
    work3819.jac.invOK = true ∧ acceptsUnitSq work3819.out = true := by decide +kernel

def cell3819 : CellCertificate where
  tauBall := tau3819
  contactCenter := center3819
  contactBall := contact3819
  work := work3819
  center_sq := center_sq3819
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3819.1
  jac_ok := checks3819.2.1
  accepted := checks3819.2.2

def tau3820 : RatBall :=
  ⟨⟨117/640, 227/640⟩, 3/1280⟩
def center3820 : GaussianRat :=
  ⟨142795751/1000000000, 246771071/1000000000⟩
def contact3820 : RatBall := localContactBall tau3820 center3820
def work3820 : RoundedTauEval :=
  evalTau precision tau3820 contact3820 logTwoBall

theorem center_sq3820 : (center3820.re : ℝ)^2 +
    (center3820.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3820]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3820 : work3820.theta.ok = true ∧
    work3820.jac.invOK = true ∧ acceptsUnitSq work3820.out = true := by decide +kernel

def cell3820 : CellCertificate where
  tauBall := tau3820
  contactCenter := center3820
  contactBall := contact3820
  work := work3820
  center_sq := center_sq3820
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3820.1
  jac_ok := checks3820.2.1
  accepted := checks3820.2.2

def tau3821 : RatBall :=
  ⟨⟨119/640, 227/640⟩, 3/1280⟩
def center3821 : GaussianRat :=
  ⟨145138173/1000000000, 123210011/500000000⟩
def contact3821 : RatBall := localContactBall tau3821 center3821
def work3821 : RoundedTauEval :=
  evalTau precision tau3821 contact3821 logTwoBall

theorem center_sq3821 : (center3821.re : ℝ)^2 +
    (center3821.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3821]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3821 : work3821.theta.ok = true ∧
    work3821.jac.invOK = true ∧ acceptsUnitSq work3821.out = true := by decide +kernel

def cell3821 : CellCertificate where
  tauBall := tau3821
  contactCenter := center3821
  contactBall := contact3821
  work := work3821
  center_sq := center_sq3821
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3821.1
  jac_ok := checks3821.2.1
  accepted := checks3821.2.2

def tau3822 : RatBall :=
  ⟨⟨113/640, 229/640⟩, 3/1280⟩
def center3822 : GaussianRat :=
  ⟨69219087/500000000, 49963011/200000000⟩
def contact3822 : RatBall := localContactBall tau3822 center3822
def work3822 : RoundedTauEval :=
  evalTau precision tau3822 contact3822 logTwoBall

theorem center_sq3822 : (center3822.re : ℝ)^2 +
    (center3822.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3822]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3822 : work3822.theta.ok = true ∧
    work3822.jac.invOK = true ∧ acceptsUnitSq work3822.out = true := by decide +kernel

def cell3822 : CellCertificate where
  tauBall := tau3822
  contactCenter := center3822
  contactBall := contact3822
  work := work3822
  center_sq := center_sq3822
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3822.1
  jac_ok := checks3822.2.1
  accepted := checks3822.2.2

def tau3823 : RatBall :=
  ⟨⟨23/128, 229/640⟩, 3/1280⟩
def center3823 : GaussianRat :=
  ⟨70397387/500000000, 249469121/1000000000⟩
def contact3823 : RatBall := localContactBall tau3823 center3823
def work3823 : RoundedTauEval :=
  evalTau precision tau3823 contact3823 logTwoBall

theorem center_sq3823 : (center3823.re : ℝ)^2 +
    (center3823.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3823]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3823 : work3823.theta.ok = true ∧
    work3823.jac.invOK = true ∧ acceptsUnitSq work3823.out = true := by decide +kernel

def cell3823 : CellCertificate where
  tauBall := tau3823
  contactCenter := center3823
  contactBall := contact3823
  work := work3823
  center_sq := center_sq3823
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3823.1
  jac_ok := checks3823.2.1
  accepted := checks3823.2.2

def cells : List CellCertificate := [cell3816, cell3817, cell3818, cell3819, cell3820, cell3821, cell3822, cell3823]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477

end


