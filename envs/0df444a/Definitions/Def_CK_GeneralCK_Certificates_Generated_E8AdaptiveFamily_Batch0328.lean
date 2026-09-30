-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0328
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0328
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:14.74677+00:00
-- url     : https://prove2.me/theorems/d6cdfaff-a88b-4372-9fae-9e91cb63f785
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0328.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2624 : RatBall :=
  ⟨⟨-97/640, -231/640⟩, 3/1280⟩
def center2624 : GaussianRat :=
  ⟨-59864687/500000000, -254794957/1000000000⟩
def contact2624 : RatBall := localContactBall tau2624 center2624
def work2624 : RoundedTauEval :=
  evalTau precision tau2624 contact2624 logTwoBall

theorem center_sq2624 : (center2624.re : ℝ)^2 +
    (center2624.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2624]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2624 : work2624.theta.ok = true ∧
    work2624.jac.invOK = true ∧ acceptsUnitSq work2624.out = true := by decide +kernel

def cell2624 : CellCertificate where
  tauBall := tau2624
  contactCenter := center2624
  contactBall := contact2624
  work := work2624
  center_sq := center_sq2624
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2624.1
  jac_ok := checks2624.2.1
  accepted := checks2624.2.2

def tau2625 : RatBall :=
  ⟨⟨-99/640, -229/640⟩, 3/1280⟩
def center2625 : GaussianRat :=
  ⟨-30454243/250000000, -126047019/500000000⟩
def contact2625 : RatBall := localContactBall tau2625 center2625
def work2625 : RoundedTauEval :=
  evalTau precision tau2625 contact2625 logTwoBall

theorem center_sq2625 : (center2625.re : ℝ)^2 +
    (center2625.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2625 : work2625.theta.ok = true ∧
    work2625.jac.invOK = true ∧ acceptsUnitSq work2625.out = true := by decide +kernel

def cell2625 : CellCertificate where
  tauBall := tau2625
  contactCenter := center2625
  contactBall := contact2625
  work := work2625
  center_sq := center_sq2625
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2625.1
  jac_ok := checks2625.2.1
  accepted := checks2625.2.2

def tau2626 : RatBall :=
  ⟨⟨-97/640, -229/640⟩, 3/1280⟩
def center2626 : GaussianRat :=
  ⟨-119425411/1000000000, -252398639/1000000000⟩
def contact2626 : RatBall := localContactBall tau2626 center2626
def work2626 : RoundedTauEval :=
  evalTau precision tau2626 contact2626 logTwoBall

theorem center_sq2626 : (center2626.re : ℝ)^2 +
    (center2626.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2626]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2626 : work2626.theta.ok = true ∧
    work2626.jac.invOK = true ∧ acceptsUnitSq work2626.out = true := by decide +kernel

def cell2626 : CellCertificate where
  tauBall := tau2626
  contactCenter := center2626
  contactBall := contact2626
  work := work2626
  center_sq := center_sq2626
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2626.1
  jac_ok := checks2626.2.1
  accepted := checks2626.2.2

def tau2627 : RatBall :=
  ⟨⟨-89/640, -241/640⟩, 3/1280⟩
def center2627 : GaussianRat :=
  ⟨-22313823/200000000, -13406097/50000000⟩
def contact2627 : RatBall := localContactBall tau2627 center2627
def work2627 : RoundedTauEval :=
  evalTau precision tau2627 contact2627 logTwoBall

theorem center_sq2627 : (center2627.re : ℝ)^2 +
    (center2627.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2627]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2627 : work2627.theta.ok = true ∧
    work2627.jac.invOK = true ∧ acceptsUnitSq work2627.out = true := by decide +kernel

def cell2627 : CellCertificate where
  tauBall := tau2627
  contactCenter := center2627
  contactBall := contact2627
  work := work2627
  center_sq := center_sq2627
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2627.1
  jac_ok := checks2627.2.1
  accepted := checks2627.2.2

def tau2628 : RatBall :=
  ⟨⟨-87/640, -241/640⟩, 3/1280⟩
def center2628 : GaussianRat :=
  ⟨-109122947/1000000000, -53684517/200000000⟩
def contact2628 : RatBall := localContactBall tau2628 center2628
def work2628 : RoundedTauEval :=
  evalTau precision tau2628 contact2628 logTwoBall

theorem center_sq2628 : (center2628.re : ℝ)^2 +
    (center2628.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2628]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2628 : work2628.theta.ok = true ∧
    work2628.jac.invOK = true ∧ acceptsUnitSq work2628.out = true := by decide +kernel

def cell2628 : CellCertificate where
  tauBall := tau2628
  contactCenter := center2628
  contactBall := contact2628
  work := work2628
  center_sq := center_sq2628
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2628.1
  jac_ok := checks2628.2.1
  accepted := checks2628.2.2

def tau2629 : RatBall :=
  ⟨⟨-17/128, -241/640⟩, 3/1280⟩
def center2629 : GaussianRat :=
  ⟨-53336381/500000000, -268717167/1000000000⟩
def contact2629 : RatBall := localContactBall tau2629 center2629
def work2629 : RoundedTauEval :=
  evalTau precision tau2629 contact2629 logTwoBall

theorem center_sq2629 : (center2629.re : ℝ)^2 +
    (center2629.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2629]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2629 : work2629.theta.ok = true ∧
    work2629.jac.invOK = true ∧ acceptsUnitSq work2629.out = true := by decide +kernel

def cell2629 : CellCertificate where
  tauBall := tau2629
  contactCenter := center2629
  contactBall := contact2629
  work := work2629
  center_sq := center_sq2629
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2629.1
  jac_ok := checks2629.2.1
  accepted := checks2629.2.2

def tau2630 : RatBall :=
  ⟨⟨-83/640, -243/640⟩, 3/1280⟩
def center2630 : GaussianRat :=
  ⟨-4180239/40000000, -271464801/1000000000⟩
def contact2630 : RatBall := localContactBall tau2630 center2630
def work2630 : RoundedTauEval :=
  evalTau precision tau2630 contact2630 logTwoBall

theorem center_sq2630 : (center2630.re : ℝ)^2 +
    (center2630.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2630 : work2630.theta.ok = true ∧
    work2630.jac.invOK = true ∧ acceptsUnitSq work2630.out = true := by decide +kernel

def cell2630 : CellCertificate where
  tauBall := tau2630
  contactCenter := center2630
  contactBall := contact2630
  work := work2630
  center_sq := center_sq2630
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2630.1
  jac_ok := checks2630.2.1
  accepted := checks2630.2.2

def tau2631 : RatBall :=
  ⟨⟨-81/640, -243/640⟩, 3/1280⟩
def center2631 : GaussianRat :=
  ⟨-51020881/500000000, -135875479/500000000⟩
def contact2631 : RatBall := localContactBall tau2631 center2631
def work2631 : RoundedTauEval :=
  evalTau precision tau2631 contact2631 logTwoBall

theorem center_sq2631 : (center2631.re : ℝ)^2 +
    (center2631.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2631]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2631 : work2631.theta.ok = true ∧
    work2631.jac.invOK = true ∧ acceptsUnitSq work2631.out = true := by decide +kernel

def cell2631 : CellCertificate where
  tauBall := tau2631
  contactCenter := center2631
  contactBall := contact2631
  work := work2631
  center_sq := center_sq2631
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2631.1
  jac_ok := checks2631.2.1
  accepted := checks2631.2.2

def cells : List CellCertificate := [cell2624, cell2625, cell2626, cell2627, cell2628, cell2629, cell2630, cell2631]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328

end


