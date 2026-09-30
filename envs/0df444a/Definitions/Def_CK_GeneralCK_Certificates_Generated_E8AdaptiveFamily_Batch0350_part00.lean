-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0350_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:16:23.132964+00:00
-- url     : https://prove2.me/theorems/fe097deb-689f-4586-9769-253350062be6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0350 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2800 : RatBall :=
  ⟨⟨-39/640, -247/640⟩, 3/1280⟩
def center2800 : GaussianRat :=
  ⟨-49825917/1000000000, -281309513/1000000000⟩
def contact2800 : RatBall := localContactBall tau2800 center2800
def work2800 : RoundedTauEval :=
  evalTau precision tau2800 contact2800 logTwoBall

theorem center_sq2800 : (center2800.re : ℝ)^2 +
    (center2800.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2800]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2800 : work2800.theta.ok = true ∧
    work2800.jac.invOK = true ∧ acceptsUnitSq work2800.out = true := by decide +kernel

def cell2800 : CellCertificate where
  tauBall := tau2800
  contactCenter := center2800
  contactBall := contact2800
  work := work2800
  center_sq := center_sq2800
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2800.1
  jac_ok := checks2800.2.1
  accepted := checks2800.2.2

def tau2801 : RatBall :=
  ⟨⟨-37/640, -247/640⟩, 3/1280⟩
def center2801 : GaussianRat :=
  ⟨-11820737/250000000, -11258061/40000000⟩
def contact2801 : RatBall := localContactBall tau2801 center2801
def work2801 : RoundedTauEval :=
  evalTau precision tau2801 contact2801 logTwoBall

theorem center_sq2801 : (center2801.re : ℝ)^2 +
    (center2801.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2801]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2801 : work2801.theta.ok = true ∧
    work2801.jac.invOK = true ∧ acceptsUnitSq work2801.out = true := by decide +kernel

def cell2801 : CellCertificate where
  tauBall := tau2801
  contactCenter := center2801
  contactBall := contact2801
  work := work2801
  center_sq := center_sq2801
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2801.1
  jac_ok := checks2801.2.1
  accepted := checks2801.2.2

def tau2802 : RatBall :=
  ⟨⟨-39/640, -49/128⟩, 3/1280⟩
def center2802 : GaussianRat :=
  ⟨-49681259/1000000000, -139385581/500000000⟩
def contact2802 : RatBall := localContactBall tau2802 center2802
def work2802 : RoundedTauEval :=
  evalTau precision tau2802 contact2802 logTwoBall

theorem center_sq2802 : (center2802.re : ℝ)^2 +
    (center2802.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2802]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2802 : work2802.theta.ok = true ∧
    work2802.jac.invOK = true ∧ acceptsUnitSq work2802.out = true := by decide +kernel

def cell2802 : CellCertificate where
  tauBall := tau2802
  contactCenter := center2802
  contactBall := contact2802
  work := work2802
  center_sq := center_sq2802
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2802.1
  jac_ok := checks2802.2.1
  accepted := checks2802.2.2

def tau2803 : RatBall :=
  ⟨⟨-37/640, -49/128⟩, 3/1280⟩
def center2803 : GaussianRat :=
  ⟨-23572771/500000000, -278911223/1000000000⟩
def contact2803 : RatBall := localContactBall tau2803 center2803
def work2803 : RoundedTauEval :=
  evalTau precision tau2803 contact2803 logTwoBall

theorem center_sq2803 : (center2803.re : ℝ)^2 +
    (center2803.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2803]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2803 : work2803.theta.ok = true ∧
    work2803.jac.invOK = true ∧ acceptsUnitSq work2803.out = true := by decide +kernel

def cell2803 : CellCertificate where
  tauBall := tau2803
  contactCenter := center2803
  contactBall := contact2803
  work := work2803
  center_sq := center_sq2803
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2803.1
  jac_ok := checks2803.2.1
  accepted := checks2803.2.2

def tau2804 : RatBall :=
  ⟨⟨-7/128, -247/640⟩, 3/1280⟩
def center2804 : GaussianRat :=
  ⟨-2796129/62500000, -281586221/1000000000⟩
def contact2804 : RatBall := localContactBall tau2804 center2804
def work2804 : RoundedTauEval :=
  evalTau precision tau2804 contact2804 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350


