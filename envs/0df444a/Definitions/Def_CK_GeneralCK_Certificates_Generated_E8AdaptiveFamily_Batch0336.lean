-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0336
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0336
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:42:35.780833+00:00
-- url     : https://prove2.me/theorems/986519fa-be77-4c70-b57a-51472af7f309
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0336.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2688 : RatBall :=
  ⟨⟨-17/128, -233/640⟩, 3/1280⟩
def center2688 : GaussianRat :=
  ⟨-105537631/1000000000, -258956581/1000000000⟩
def contact2688 : RatBall := localContactBall tau2688 center2688
def work2688 : RoundedTauEval :=
  evalTau precision tau2688 contact2688 logTwoBall

theorem center_sq2688 : (center2688.re : ℝ)^2 +
    (center2688.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2688]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2688 : work2688.theta.ok = true ∧
    work2688.jac.invOK = true ∧ acceptsUnitSq work2688.out = true := by decide +kernel

def cell2688 : CellCertificate where
  tauBall := tau2688
  contactCenter := center2688
  contactBall := contact2688
  work := work2688
  center_sq := center_sq2688
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2688.1
  jac_ok := checks2688.2.1
  accepted := checks2688.2.2

def tau2689 : RatBall :=
  ⟨⟨-83/640, -47/128⟩, 3/1280⟩
def center2689 : GaussianRat :=
  ⟨-25844903/250000000, -261664807/1000000000⟩
def contact2689 : RatBall := localContactBall tau2689 center2689
def work2689 : RoundedTauEval :=
  evalTau precision tau2689 contact2689 logTwoBall

theorem center_sq2689 : (center2689.re : ℝ)^2 +
    (center2689.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2689]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2689 : work2689.theta.ok = true ∧
    work2689.jac.invOK = true ∧ acceptsUnitSq work2689.out = true := by decide +kernel

def cell2689 : CellCertificate where
  tauBall := tau2689
  contactCenter := center2689
  contactBall := contact2689
  work := work2689
  center_sq := center_sq2689
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2689.1
  jac_ok := checks2689.2.1
  accepted := checks2689.2.2

def tau2690 : RatBall :=
  ⟨⟨-81/640, -47/128⟩, 3/1280⟩
def center2690 : GaussianRat :=
  ⟨-100939831/1000000000, -261935857/1000000000⟩
def contact2690 : RatBall := localContactBall tau2690 center2690
def work2690 : RoundedTauEval :=
  evalTau precision tau2690 contact2690 logTwoBall

theorem center_sq2690 : (center2690.re : ℝ)^2 +
    (center2690.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2690]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2690 : work2690.theta.ok = true ∧
    work2690.jac.invOK = true ∧ acceptsUnitSq work2690.out = true := by decide +kernel

def cell2690 : CellCertificate where
  tauBall := tau2690
  contactCenter := center2690
  contactBall := contact2690
  work := work2690
  center_sq := center_sq2690
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2690.1
  jac_ok := checks2690.2.1
  accepted := checks2690.2.2

def tau2691 : RatBall :=
  ⟨⟨-83/640, -233/640⟩, 3/1280⟩
def center2691 : GaussianRat :=
  ⟨-103107441/1000000000, -129614913/500000000⟩
def contact2691 : RatBall := localContactBall tau2691 center2691
def work2691 : RoundedTauEval :=
  evalTau precision tau2691 contact2691 logTwoBall

theorem center_sq2691 : (center2691.re : ℝ)^2 +
    (center2691.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2691]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2691 : work2691.theta.ok = true ∧
    work2691.jac.invOK = true ∧ acceptsUnitSq work2691.out = true := by decide +kernel

def cell2691 : CellCertificate where
  tauBall := tau2691
  contactCenter := center2691
  contactBall := contact2691
  work := work2691
  center_sq := center_sq2691
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2691.1
  jac_ok := checks2691.2.1
  accepted := checks2691.2.2

def tau2692 : RatBall :=
  ⟨⟨-81/640, -233/640⟩, 3/1280⟩
def center2692 : GaussianRat :=
  ⟨-12584197/125000000, -1013661/3906250⟩
def contact2692 : RatBall := localContactBall tau2692 center2692
def work2692 : RoundedTauEval :=
  evalTau precision tau2692 contact2692 logTwoBall

theorem center_sq2692 : (center2692.re : ℝ)^2 +
    (center2692.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2692]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2692 : work2692.theta.ok = true ∧
    work2692.jac.invOK = true ∧ acceptsUnitSq work2692.out = true := by decide +kernel

def cell2692 : CellCertificate where
  tauBall := tau2692
  contactCenter := center2692
  contactBall := contact2692
  work := work2692
  center_sq := center_sq2692
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2692.1
  jac_ok := checks2692.2.1
  accepted := checks2692.2.2

def tau2693 : RatBall :=
  ⟨⟨-19/128, -231/640⟩, 3/1280⟩
def center2693 : GaussianRat :=
  ⟨-117328287/1000000000, -255098241/1000000000⟩
def contact2693 : RatBall := localContactBall tau2693 center2693
def work2693 : RoundedTauEval :=
  evalTau precision tau2693 contact2693 logTwoBall

theorem center_sq2693 : (center2693.re : ℝ)^2 +
    (center2693.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2693]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2693 : work2693.theta.ok = true ∧
    work2693.jac.invOK = true ∧ acceptsUnitSq work2693.out = true := by decide +kernel

def cell2693 : CellCertificate where
  tauBall := tau2693
  contactCenter := center2693
  contactBall := contact2693
  work := work2693
  center_sq := center_sq2693
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2693.1
  jac_ok := checks2693.2.1
  accepted := checks2693.2.2

def tau2694 : RatBall :=
  ⟨⟨-93/640, -231/640⟩, 3/1280⟩
def center2694 : GaussianRat :=
  ⟨-114923139/1000000000, -12769801/50000000⟩
def contact2694 : RatBall := localContactBall tau2694 center2694
def work2694 : RoundedTauEval :=
  evalTau precision tau2694 contact2694 logTwoBall

theorem center_sq2694 : (center2694.re : ℝ)^2 +
    (center2694.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2694]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2694 : work2694.theta.ok = true ∧
    work2694.jac.invOK = true ∧ acceptsUnitSq work2694.out = true := by decide +kernel

def cell2694 : CellCertificate where
  tauBall := tau2694
  contactCenter := center2694
  contactBall := contact2694
  work := work2694
  center_sq := center_sq2694
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2694.1
  jac_ok := checks2694.2.1
  accepted := checks2694.2.2

def tau2695 : RatBall :=
  ⟨⟨-19/128, -229/640⟩, 3/1280⟩
def center2695 : GaussianRat :=
  ⟨-117029769/1000000000, -63174463/250000000⟩
def contact2695 : RatBall := localContactBall tau2695 center2695
def work2695 : RoundedTauEval :=
  evalTau precision tau2695 contact2695 logTwoBall

theorem center_sq2695 : (center2695.re : ℝ)^2 +
    (center2695.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2695]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2695 : work2695.theta.ok = true ∧
    work2695.jac.invOK = true ∧ acceptsUnitSq work2695.out = true := by decide +kernel

def cell2695 : CellCertificate where
  tauBall := tau2695
  contactCenter := center2695
  contactBall := contact2695
  work := work2695
  center_sq := center_sq2695
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2695.1
  jac_ok := checks2695.2.1
  accepted := checks2695.2.2

def cells : List CellCertificate := [cell2688, cell2689, cell2690, cell2691, cell2692, cell2693, cell2694, cell2695]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336

end


