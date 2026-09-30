-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0337
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0337
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:55:43.540864+00:00
-- url     : https://prove2.me/theorems/f8467a82-599b-4d75-ae3b-3d1e65811043
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0337.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2696 : RatBall :=
  ⟨⟨-93/640, -229/640⟩, 3/1280⟩
def center2696 : GaussianRat :=
  ⟨-28657529/250000000, -252991629/1000000000⟩
def contact2696 : RatBall := localContactBall tau2696 center2696
def work2696 : RoundedTauEval :=
  evalTau precision tau2696 contact2696 logTwoBall

theorem center_sq2696 : (center2696.re : ℝ)^2 +
    (center2696.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2696]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2696 : work2696.theta.ok = true ∧
    work2696.jac.invOK = true ∧ acceptsUnitSq work2696.out = true := by decide +kernel

def cell2696 : CellCertificate where
  tauBall := tau2696
  contactCenter := center2696
  contactBall := contact2696
  work := work2696
  center_sq := center_sq2696
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2696.1
  jac_ok := checks2696.2.1
  accepted := checks2696.2.2

def tau2697 : RatBall :=
  ⟨⟨-79/640, -239/640⟩, 3/1280⟩
def center2697 : GaussianRat :=
  ⟨-99027743/1000000000, -267103523/1000000000⟩
def contact2697 : RatBall := localContactBall tau2697 center2697
def work2697 : RoundedTauEval :=
  evalTau precision tau2697 contact2697 logTwoBall

theorem center_sq2697 : (center2697.re : ℝ)^2 +
    (center2697.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2697]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2697 : work2697.theta.ok = true ∧
    work2697.jac.invOK = true ∧ acceptsUnitSq work2697.out = true := by decide +kernel

def cell2697 : CellCertificate where
  tauBall := tau2697
  contactCenter := center2697
  contactBall := contact2697
  work := work2697
  center_sq := center_sq2697
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2697.1
  jac_ok := checks2697.2.1
  accepted := checks2697.2.2

def tau2698 : RatBall :=
  ⟨⟨-77/640, -239/640⟩, 3/1280⟩
def center2698 : GaussianRat :=
  ⟨-96568507/1000000000, -66842431/250000000⟩
def contact2698 : RatBall := localContactBall tau2698 center2698
def work2698 : RoundedTauEval :=
  evalTau precision tau2698 contact2698 logTwoBall

theorem center_sq2698 : (center2698.re : ℝ)^2 +
    (center2698.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2698]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2698 : work2698.theta.ok = true ∧
    work2698.jac.invOK = true ∧ acceptsUnitSq work2698.out = true := by decide +kernel

def cell2698 : CellCertificate where
  tauBall := tau2698
  contactCenter := center2698
  contactBall := contact2698
  work := work2698
  center_sq := center_sq2698
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2698.1
  jac_ok := checks2698.2.1
  accepted := checks2698.2.2

def tau2699 : RatBall :=
  ⟨⟨-79/640, -237/640⟩, 3/1280⟩
def center2699 : GaussianRat :=
  ⟨-98760267/1000000000, -132324589/500000000⟩
def contact2699 : RatBall := localContactBall tau2699 center2699
def work2699 : RoundedTauEval :=
  evalTau precision tau2699 contact2699 logTwoBall

theorem center_sq2699 : (center2699.re : ℝ)^2 +
    (center2699.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2699]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2699 : work2699.theta.ok = true ∧
    work2699.jac.invOK = true ∧ acceptsUnitSq work2699.out = true := by decide +kernel

def cell2699 : CellCertificate where
  tauBall := tau2699
  contactCenter := center2699
  contactBall := contact2699
  work := work2699
  center_sq := center_sq2699
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2699.1
  jac_ok := checks2699.2.1
  accepted := checks2699.2.2

def tau2700 : RatBall :=
  ⟨⟨-77/640, -237/640⟩, 3/1280⟩
def center2700 : GaussianRat :=
  ⟨-96307191/1000000000, -264911783/1000000000⟩
def contact2700 : RatBall := localContactBall tau2700 center2700
def work2700 : RoundedTauEval :=
  evalTau precision tau2700 contact2700 logTwoBall

theorem center_sq2700 : (center2700.re : ℝ)^2 +
    (center2700.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2700]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2700 : work2700.theta.ok = true ∧
    work2700.jac.invOK = true ∧ acceptsUnitSq work2700.out = true := by decide +kernel

def cell2700 : CellCertificate where
  tauBall := tau2700
  contactCenter := center2700
  contactBall := contact2700
  work := work2700
  center_sq := center_sq2700
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2700.1
  jac_ok := checks2700.2.1
  accepted := checks2700.2.2

def tau2701 : RatBall :=
  ⟨⟨-15/128, -239/640⟩, 3/1280⟩
def center2701 : GaussianRat :=
  ⟨-23526423/250000000, -133814851/500000000⟩
def contact2701 : RatBall := localContactBall tau2701 center2701
def work2701 : RoundedTauEval :=
  evalTau precision tau2701 contact2701 logTwoBall

theorem center_sq2701 : (center2701.re : ℝ)^2 +
    (center2701.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2701]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2701 : work2701.theta.ok = true ∧
    work2701.jac.invOK = true ∧ acceptsUnitSq work2701.out = true := by decide +kernel

def cell2701 : CellCertificate where
  tauBall := tau2701
  contactCenter := center2701
  contactBall := contact2701
  work := work2701
  center_sq := center_sq2701
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2701.1
  jac_ok := checks2701.2.1
  accepted := checks2701.2.2

def tau2702 : RatBall :=
  ⟨⟨-73/640, -239/640⟩, 3/1280⟩
def center2702 : GaussianRat :=
  ⟨-91639379/1000000000, -267883413/1000000000⟩
def contact2702 : RatBall := localContactBall tau2702 center2702
def work2702 : RoundedTauEval :=
  evalTau precision tau2702 contact2702 logTwoBall

theorem center_sq2702 : (center2702.re : ℝ)^2 +
    (center2702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2702 : work2702.theta.ok = true ∧
    work2702.jac.invOK = true ∧ acceptsUnitSq work2702.out = true := by decide +kernel

def cell2702 : CellCertificate where
  tauBall := tau2702
  contactCenter := center2702
  contactBall := contact2702
  work := work2702
  center_sq := center_sq2702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2702.1
  jac_ok := checks2702.2.1
  accepted := checks2702.2.2

def tau2703 : RatBall :=
  ⟨⟨-15/128, -237/640⟩, 3/1280⟩
def center2703 : GaussianRat :=
  ⟨-46925291/500000000, -53033649/200000000⟩
def contact2703 : RatBall := localContactBall tau2703 center2703
def work2703 : RoundedTauEval :=
  evalTau precision tau2703 contact2703 logTwoBall

theorem center_sq2703 : (center2703.re : ℝ)^2 +
    (center2703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2703 : work2703.theta.ok = true ∧
    work2703.jac.invOK = true ∧ acceptsUnitSq work2703.out = true := by decide +kernel

def cell2703 : CellCertificate where
  tauBall := tau2703
  contactCenter := center2703
  contactBall := contact2703
  work := work2703
  center_sq := center_sq2703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2703.1
  jac_ok := checks2703.2.1
  accepted := checks2703.2.2

def cells : List CellCertificate := [cell2696, cell2697, cell2698, cell2699, cell2700, cell2701, cell2702, cell2703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337

end


