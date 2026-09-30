-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0329
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0329
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:12:05.732862+00:00
-- url     : https://prove2.me/theorems/57f6e5de-c95a-4ea4-bf98-5a19baca2a8d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0329.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2632 : RatBall :=
  ⟨⟨-83/640, -241/640⟩, 3/1280⟩
def center2632 : GaussianRat :=
  ⟨-104218637/1000000000, -134502819/500000000⟩
def contact2632 : RatBall := localContactBall tau2632 center2632
def work2632 : RoundedTauEval :=
  evalTau precision tau2632 contact2632 logTwoBall

theorem center_sq2632 : (center2632.re : ℝ)^2 +
    (center2632.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2632]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2632 : work2632.theta.ok = true ∧
    work2632.jac.invOK = true ∧ acceptsUnitSq work2632.out = true := by decide +kernel

def cell2632 : CellCertificate where
  tauBall := tau2632
  contactCenter := center2632
  contactBall := contact2632
  work := work2632
  center_sq := center_sq2632
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2632.1
  jac_ok := checks2632.2.1
  accepted := checks2632.2.2

def tau2633 : RatBall :=
  ⟨⟨-81/640, -241/640⟩, 3/1280⟩
def center2633 : GaussianRat :=
  ⟨-101760649/1000000000, -269287947/1000000000⟩
def contact2633 : RatBall := localContactBall tau2633 center2633
def work2633 : RoundedTauEval :=
  evalTau precision tau2633 contact2633 logTwoBall

theorem center_sq2633 : (center2633.re : ℝ)^2 +
    (center2633.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2633]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2633 : work2633.theta.ok = true ∧
    work2633.jac.invOK = true ∧ acceptsUnitSq work2633.out = true := by decide +kernel

def cell2633 : CellCertificate where
  tauBall := tau2633
  contactCenter := center2633
  contactBall := contact2633
  work := work2633
  center_sq := center_sq2633
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2633.1
  jac_ok := checks2633.2.1
  accepted := checks2633.2.2

def tau2634 : RatBall :=
  ⟨⟨-77/640, -49/128⟩, 3/1280⟩
def center2634 : GaussianRat :=
  ⟨-24343527/250000000, -34347651/125000000⟩
def contact2634 : RatBall := localContactBall tau2634 center2634
def work2634 : RoundedTauEval :=
  evalTau precision tau2634 contact2634 logTwoBall

theorem center_sq2634 : (center2634.re : ℝ)^2 +
    (center2634.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2634]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2634 : work2634.theta.ok = true ∧
    work2634.jac.invOK = true ∧ acceptsUnitSq work2634.out = true := by decide +kernel

def cell2634 : CellCertificate where
  tauBall := tau2634
  contactCenter := center2634
  contactBall := contact2634
  work := work2634
  center_sq := center_sq2634
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2634.1
  jac_ok := checks2634.2.1
  accepted := checks2634.2.2

def tau2635 : RatBall :=
  ⟨⟨-15/128, -49/128⟩, 3/1280⟩
def center2635 : GaussianRat :=
  ⟨-9489219/100000000, -275052007/1000000000⟩
def contact2635 : RatBall := localContactBall tau2635 center2635
def work2635 : RoundedTauEval :=
  evalTau precision tau2635 contact2635 logTwoBall

theorem center_sq2635 : (center2635.re : ℝ)^2 +
    (center2635.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2635]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2635 : work2635.theta.ok = true ∧
    work2635.jac.invOK = true ∧ acceptsUnitSq work2635.out = true := by decide +kernel

def cell2635 : CellCertificate where
  tauBall := tau2635
  contactCenter := center2635
  contactBall := contact2635
  work := work2635
  center_sq := center_sq2635
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2635.1
  jac_ok := checks2635.2.1
  accepted := checks2635.2.2

def tau2636 : RatBall :=
  ⟨⟨-73/640, -49/128⟩, 3/1280⟩
def center2636 : GaussianRat :=
  ⟨-92406637/1000000000, -275316291/1000000000⟩
def contact2636 : RatBall := localContactBall tau2636 center2636
def work2636 : RoundedTauEval :=
  evalTau precision tau2636 contact2636 logTwoBall

theorem center_sq2636 : (center2636.re : ℝ)^2 +
    (center2636.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2636]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2636 : work2636.theta.ok = true ∧
    work2636.jac.invOK = true ∧ acceptsUnitSq work2636.out = true := by decide +kernel

def cell2636 : CellCertificate where
  tauBall := tau2636
  contactCenter := center2636
  contactBall := contact2636
  work := work2636
  center_sq := center_sq2636
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2636.1
  jac_ok := checks2636.2.1
  accepted := checks2636.2.2

def tau2637 : RatBall :=
  ⟨⟨-79/640, -243/640⟩, 3/1280⟩
def center2637 : GaussianRat :=
  ⟨-24893429/250000000, -136015413/500000000⟩
def contact2637 : RatBall := localContactBall tau2637 center2637
def work2637 : RoundedTauEval :=
  evalTau precision tau2637 contact2637 logTwoBall

theorem center_sq2637 : (center2637.re : ℝ)^2 +
    (center2637.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2637]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2637 : work2637.theta.ok = true ∧
    work2637.jac.invOK = true ∧ acceptsUnitSq work2637.out = true := by decide +kernel

def cell2637 : CellCertificate where
  tauBall := tau2637
  contactCenter := center2637
  contactBall := contact2637
  work := work2637
  center_sq := center_sq2637
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2637.1
  jac_ok := checks2637.2.1
  accepted := checks2637.2.2

def tau2638 : RatBall :=
  ⟨⟨-77/640, -243/640⟩, 3/1280⟩
def center2638 : GaussianRat :=
  ⟨-97101919/1000000000, -68076089/250000000⟩
def contact2638 : RatBall := localContactBall tau2638 center2638
def work2638 : RoundedTauEval :=
  evalTau precision tau2638 contact2638 logTwoBall

theorem center_sq2638 : (center2638.re : ℝ)^2 +
    (center2638.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2638]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2638 : work2638.theta.ok = true ∧
    work2638.jac.invOK = true ∧ acceptsUnitSq work2638.out = true := by decide +kernel

def cell2638 : CellCertificate where
  tauBall := tau2638
  contactCenter := center2638
  contactBall := contact2638
  work := work2638
  center_sq := center_sq2638
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2638.1
  jac_ok := checks2638.2.1
  accepted := checks2638.2.2

def tau2639 : RatBall :=
  ⟨⟨-79/640, -241/640⟩, 3/1280⟩
def center2639 : GaussianRat :=
  ⟨-99298877/1000000000, -134782023/500000000⟩
def contact2639 : RatBall := localContactBall tau2639 center2639
def work2639 : RoundedTauEval :=
  evalTau precision tau2639 contact2639 logTwoBall

theorem center_sq2639 : (center2639.re : ℝ)^2 +
    (center2639.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2639]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2639 : work2639.theta.ok = true ∧
    work2639.jac.invOK = true ∧ acceptsUnitSq work2639.out = true := by decide +kernel

def cell2639 : CellCertificate where
  tauBall := tau2639
  contactCenter := center2639
  contactBall := contact2639
  work := work2639
  center_sq := center_sq2639
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2639.1
  jac_ok := checks2639.2.1
  accepted := checks2639.2.2

def cells : List CellCertificate := [cell2632, cell2633, cell2634, cell2635, cell2636, cell2637, cell2638, cell2639]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329

end


