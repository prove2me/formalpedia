-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0462
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0462
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:50:49.95499+00:00
-- url     : https://prove2.me/theorems/728e6639-a54f-4bad-8235-55b9660a9fc1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0462.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3696 : RatBall :=
  ⟨⟨67/640, 237/640⟩, 3/1280⟩
def center3696 : GaussianRat :=
  ⟨20997603/250000000, 266131799/1000000000⟩
def contact3696 : RatBall := localContactBall tau3696 center3696
def work3696 : RoundedTauEval :=
  evalTau precision tau3696 contact3696 logTwoBall

theorem center_sq3696 : (center3696.re : ℝ)^2 +
    (center3696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3696 : work3696.theta.ok = true ∧
    work3696.jac.invOK = true ∧ acceptsUnitSq work3696.out = true := by decide +kernel

def cell3696 : CellCertificate where
  tauBall := tau3696
  contactCenter := center3696
  contactBall := contact3696
  work := work3696
  center_sq := center_sq3696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3696.1
  jac_ok := checks3696.2.1
  accepted := checks3696.2.2

def tau3697 : RatBall :=
  ⟨⟨13/128, 239/640⟩, 3/1280⟩
def center3697 : GaussianRat :=
  ⟨81740791/1000000000, 268834717/1000000000⟩
def contact3697 : RatBall := localContactBall tau3697 center3697
def work3697 : RoundedTauEval :=
  evalTau precision tau3697 contact3697 logTwoBall

theorem center_sq3697 : (center3697.re : ℝ)^2 +
    (center3697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3697 : work3697.theta.ok = true ∧
    work3697.jac.invOK = true ∧ acceptsUnitSq work3697.out = true := by decide +kernel

def cell3697 : CellCertificate where
  tauBall := tau3697
  contactCenter := center3697
  contactBall := contact3697
  work := work3697
  center_sq := center_sq3697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3697.1
  jac_ok := checks3697.2.1
  accepted := checks3697.2.2

def tau3698 : RatBall :=
  ⟨⟨67/640, 239/640⟩, 3/1280⟩
def center3698 : GaussianRat :=
  ⟨5263767/62500000, 134303253/500000000⟩
def contact3698 : RatBall := localContactBall tau3698 center3698
def work3698 : RoundedTauEval :=
  evalTau precision tau3698 contact3698 logTwoBall

theorem center_sq3698 : (center3698.re : ℝ)^2 +
    (center3698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3698 : work3698.theta.ok = true ∧
    work3698.jac.invOK = true ∧ acceptsUnitSq work3698.out = true := by decide +kernel

def cell3698 : CellCertificate where
  tauBall := tau3698
  contactCenter := center3698
  contactBall := contact3698
  work := work3698
  center_sq := center_sq3698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3698.1
  jac_ok := checks3698.2.1
  accepted := checks3698.2.2

def tau3699 : RatBall :=
  ⟨⟨69/640, 237/640⟩, 3/1280⟩
def center3699 : GaussianRat :=
  ⟨86460351/1000000000, 265900339/1000000000⟩
def contact3699 : RatBall := localContactBall tau3699 center3699
def work3699 : RoundedTauEval :=
  evalTau precision tau3699 contact3699 logTwoBall

theorem center_sq3699 : (center3699.re : ℝ)^2 +
    (center3699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3699 : work3699.theta.ok = true ∧
    work3699.jac.invOK = true ∧ acceptsUnitSq work3699.out = true := by decide +kernel

def cell3699 : CellCertificate where
  tauBall := tau3699
  contactCenter := center3699
  contactBall := contact3699
  work := work3699
  center_sq := center_sq3699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3699.1
  jac_ok := checks3699.2.1
  accepted := checks3699.2.2

def tau3700 : RatBall :=
  ⟨⟨71/640, 237/640⟩, 3/1280⟩
def center3700 : GaussianRat :=
  ⟨2223177/25000000, 53132513/200000000⟩
def contact3700 : RatBall := localContactBall tau3700 center3700
def work3700 : RoundedTauEval :=
  evalTau precision tau3700 contact3700 logTwoBall

theorem center_sq3700 : (center3700.re : ℝ)^2 +
    (center3700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3700 : work3700.theta.ok = true ∧
    work3700.jac.invOK = true ∧ acceptsUnitSq work3700.out = true := by decide +kernel

def cell3700 : CellCertificate where
  tauBall := tau3700
  contactCenter := center3700
  contactBall := contact3700
  work := work3700
  center_sq := center_sq3700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3700.1
  jac_ok := checks3700.2.1
  accepted := checks3700.2.2

def tau3701 : RatBall :=
  ⟨⟨69/640, 239/640⟩, 3/1280⟩
def center3701 : GaussianRat :=
  ⟨43348293/500000000, 268371857/1000000000⟩
def contact3701 : RatBall := localContactBall tau3701 center3701
def work3701 : RoundedTauEval :=
  evalTau precision tau3701 contact3701 logTwoBall

theorem center_sq3701 : (center3701.re : ℝ)^2 +
    (center3701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3701 : work3701.theta.ok = true ∧
    work3701.jac.invOK = true ∧ acceptsUnitSq work3701.out = true := by decide +kernel

def cell3701 : CellCertificate where
  tauBall := tau3701
  contactCenter := center3701
  contactBall := contact3701
  work := work3701
  center_sq := center_sq3701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3701.1
  jac_ok := checks3701.2.1
  accepted := checks3701.2.2

def tau3702 : RatBall :=
  ⟨⟨71/640, 239/640⟩, 3/1280⟩
def center3702 : GaussianRat :=
  ⟨89169649/1000000000, 67032703/250000000⟩
def contact3702 : RatBall := localContactBall tau3702 center3702
def work3702 : RoundedTauEval :=
  evalTau precision tau3702 contact3702 logTwoBall

theorem center_sq3702 : (center3702.re : ℝ)^2 +
    (center3702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3702 : work3702.theta.ok = true ∧
    work3702.jac.invOK = true ∧ acceptsUnitSq work3702.out = true := by decide +kernel

def cell3702 : CellCertificate where
  tauBall := tau3702
  contactCenter := center3702
  contactBall := contact3702
  work := work3702
  center_sq := center_sq3702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3702.1
  jac_ok := checks3702.2.1
  accepted := checks3702.2.2

def tau3703 : RatBall :=
  ⟨⟨73/640, 237/640⟩, 3/1280⟩
def center3703 : GaussianRat :=
  ⟨45695259/500000000, 6635463/25000000⟩
def contact3703 : RatBall := localContactBall tau3703 center3703
def work3703 : RoundedTauEval :=
  evalTau precision tau3703 contact3703 logTwoBall

theorem center_sq3703 : (center3703.re : ℝ)^2 +
    (center3703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3703 : work3703.theta.ok = true ∧
    work3703.jac.invOK = true ∧ acceptsUnitSq work3703.out = true := by decide +kernel

def cell3703 : CellCertificate where
  tauBall := tau3703
  contactCenter := center3703
  contactBall := contact3703
  work := work3703
  center_sq := center_sq3703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3703.1
  jac_ok := checks3703.2.1
  accepted := checks3703.2.2

def cells : List CellCertificate := [cell3696, cell3697, cell3698, cell3699, cell3700, cell3701, cell3702, cell3703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462

end


