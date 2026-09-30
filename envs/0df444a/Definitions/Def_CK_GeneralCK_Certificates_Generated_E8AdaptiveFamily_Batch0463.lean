-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0463
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0463
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:27.111171+00:00
-- url     : https://prove2.me/theorems/cb26c78d-1e37-486f-9cbf-bf4d80217554
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0463.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3704 : RatBall :=
  ⟨⟨15/128, 237/640⟩, 3/1280⟩
def center3704 : GaussianRat :=
  ⟨46925291/500000000, 53033649/200000000⟩
def contact3704 : RatBall := localContactBall tau3704 center3704
def work3704 : RoundedTauEval :=
  evalTau precision tau3704 contact3704 logTwoBall

theorem center_sq3704 : (center3704.re : ℝ)^2 +
    (center3704.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3704]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3704 : work3704.theta.ok = true ∧
    work3704.jac.invOK = true ∧ acceptsUnitSq work3704.out = true := by decide +kernel

def cell3704 : CellCertificate where
  tauBall := tau3704
  contactCenter := center3704
  contactBall := contact3704
  work := work3704
  center_sq := center_sq3704
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3704.1
  jac_ok := checks3704.2.1
  accepted := checks3704.2.2

def tau3705 : RatBall :=
  ⟨⟨73/640, 239/640⟩, 3/1280⟩
def center3705 : GaussianRat :=
  ⟨91639379/1000000000, 267883413/1000000000⟩
def contact3705 : RatBall := localContactBall tau3705 center3705
def work3705 : RoundedTauEval :=
  evalTau precision tau3705 contact3705 logTwoBall

theorem center_sq3705 : (center3705.re : ℝ)^2 +
    (center3705.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3705]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3705 : work3705.theta.ok = true ∧
    work3705.jac.invOK = true ∧ acceptsUnitSq work3705.out = true := by decide +kernel

def cell3705 : CellCertificate where
  tauBall := tau3705
  contactCenter := center3705
  contactBall := contact3705
  work := work3705
  center_sq := center_sq3705
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3705.1
  jac_ok := checks3705.2.1
  accepted := checks3705.2.2

def tau3706 : RatBall :=
  ⟨⟨15/128, 239/640⟩, 3/1280⟩
def center3706 : GaussianRat :=
  ⟨23526423/250000000, 133814851/500000000⟩
def contact3706 : RatBall := localContactBall tau3706 center3706
def work3706 : RoundedTauEval :=
  evalTau precision tau3706 contact3706 logTwoBall

theorem center_sq3706 : (center3706.re : ℝ)^2 +
    (center3706.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3706]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3706 : work3706.theta.ok = true ∧
    work3706.jac.invOK = true ∧ acceptsUnitSq work3706.out = true := by decide +kernel

def cell3706 : CellCertificate where
  tauBall := tau3706
  contactCenter := center3706
  contactBall := contact3706
  work := work3706
  center_sq := center_sq3706
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3706.1
  jac_ok := checks3706.2.1
  accepted := checks3706.2.2

def tau3707 : RatBall :=
  ⟨⟨77/640, 237/640⟩, 3/1280⟩
def center3707 : GaussianRat :=
  ⟨96307191/1000000000, 264911783/1000000000⟩
def contact3707 : RatBall := localContactBall tau3707 center3707
def work3707 : RoundedTauEval :=
  evalTau precision tau3707 contact3707 logTwoBall

theorem center_sq3707 : (center3707.re : ℝ)^2 +
    (center3707.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3707]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3707 : work3707.theta.ok = true ∧
    work3707.jac.invOK = true ∧ acceptsUnitSq work3707.out = true := by decide +kernel

def cell3707 : CellCertificate where
  tauBall := tau3707
  contactCenter := center3707
  contactBall := contact3707
  work := work3707
  center_sq := center_sq3707
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3707.1
  jac_ok := checks3707.2.1
  accepted := checks3707.2.2

def tau3708 : RatBall :=
  ⟨⟨79/640, 237/640⟩, 3/1280⟩
def center3708 : GaussianRat :=
  ⟨98760267/1000000000, 132324589/500000000⟩
def contact3708 : RatBall := localContactBall tau3708 center3708
def work3708 : RoundedTauEval :=
  evalTau precision tau3708 contact3708 logTwoBall

theorem center_sq3708 : (center3708.re : ℝ)^2 +
    (center3708.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3708]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3708 : work3708.theta.ok = true ∧
    work3708.jac.invOK = true ∧ acceptsUnitSq work3708.out = true := by decide +kernel

def cell3708 : CellCertificate where
  tauBall := tau3708
  contactCenter := center3708
  contactBall := contact3708
  work := work3708
  center_sq := center_sq3708
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3708.1
  jac_ok := checks3708.2.1
  accepted := checks3708.2.2

def tau3709 : RatBall :=
  ⟨⟨77/640, 239/640⟩, 3/1280⟩
def center3709 : GaussianRat :=
  ⟨96568507/1000000000, 66842431/250000000⟩
def contact3709 : RatBall := localContactBall tau3709 center3709
def work3709 : RoundedTauEval :=
  evalTau precision tau3709 contact3709 logTwoBall

theorem center_sq3709 : (center3709.re : ℝ)^2 +
    (center3709.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3709]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3709 : work3709.theta.ok = true ∧
    work3709.jac.invOK = true ∧ acceptsUnitSq work3709.out = true := by decide +kernel

def cell3709 : CellCertificate where
  tauBall := tau3709
  contactCenter := center3709
  contactBall := contact3709
  work := work3709
  center_sq := center_sq3709
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3709.1
  jac_ok := checks3709.2.1
  accepted := checks3709.2.2

def tau3710 : RatBall :=
  ⟨⟨79/640, 239/640⟩, 3/1280⟩
def center3710 : GaussianRat :=
  ⟨99027743/1000000000, 267103523/1000000000⟩
def contact3710 : RatBall := localContactBall tau3710 center3710
def work3710 : RoundedTauEval :=
  evalTau precision tau3710 contact3710 logTwoBall

theorem center_sq3710 : (center3710.re : ℝ)^2 +
    (center3710.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3710]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3710 : work3710.theta.ok = true ∧
    work3710.jac.invOK = true ∧ acceptsUnitSq work3710.out = true := by decide +kernel

def cell3710 : CellCertificate where
  tauBall := tau3710
  contactCenter := center3710
  contactBall := contact3710
  work := work3710
  center_sq := center_sq3710
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3710.1
  jac_ok := checks3710.2.1
  accepted := checks3710.2.2

def tau3711 : RatBall :=
  ⟨⟨93/640, 229/640⟩, 3/1280⟩
def center3711 : GaussianRat :=
  ⟨28657529/250000000, 252991629/1000000000⟩
def contact3711 : RatBall := localContactBall tau3711 center3711
def work3711 : RoundedTauEval :=
  evalTau precision tau3711 contact3711 logTwoBall

theorem center_sq3711 : (center3711.re : ℝ)^2 +
    (center3711.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3711]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3711 : work3711.theta.ok = true ∧
    work3711.jac.invOK = true ∧ acceptsUnitSq work3711.out = true := by decide +kernel

def cell3711 : CellCertificate where
  tauBall := tau3711
  contactCenter := center3711
  contactBall := contact3711
  work := work3711
  center_sq := center_sq3711
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3711.1
  jac_ok := checks3711.2.1
  accepted := checks3711.2.2

def cells : List CellCertificate := [cell3704, cell3705, cell3706, cell3707, cell3708, cell3709, cell3710, cell3711]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463

end


