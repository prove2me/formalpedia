-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:59:22.412987+00:00
-- url     : https://prove2.me/theorems/e09b8233-5d61-4f61-a612-316a01f079ea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0354 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2832 : RatBall :=
  ⟨⟨-23/640, -251/640⟩, 3/1280⟩
def center2832 : GaussianRat :=
  ⟨-14804897/500000000, -8980133/31250000⟩
def contact2832 : RatBall := localContactBall tau2832 center2832
def work2832 : RoundedTauEval :=
  evalTau precision tau2832 contact2832 logTwoBall

theorem center_sq2832 : (center2832.re : ℝ)^2 +
    (center2832.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2832]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2832 : work2832.theta.ok = true ∧
    work2832.jac.invOK = true ∧ acceptsUnitSq work2832.out = true := by decide +kernel

def cell2832 : CellCertificate where
  tauBall := tau2832
  contactCenter := center2832
  contactBall := contact2832
  work := work2832
  center_sq := center_sq2832
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2832.1
  jac_ok := checks2832.2.1
  accepted := checks2832.2.2

def tau2833 : RatBall :=
  ⟨⟨-21/640, -251/640⟩, 3/1280⟩
def center2833 : GaussianRat :=
  ⟨-1689949/62500000, -143724721/500000000⟩
def contact2833 : RatBall := localContactBall tau2833 center2833
def work2833 : RoundedTauEval :=
  evalTau precision tau2833 contact2833 logTwoBall

theorem center_sq2833 : (center2833.re : ℝ)^2 +
    (center2833.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2833]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2833 : work2833.theta.ok = true ∧
    work2833.jac.invOK = true ∧ acceptsUnitSq work2833.out = true := by decide +kernel

def cell2833 : CellCertificate where
  tauBall := tau2833
  contactCenter := center2833
  contactBall := contact2833
  work := work2833
  center_sq := center_sq2833
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2833.1
  jac_ok := checks2833.2.1
  accepted := checks2833.2.2

def tau2834 : RatBall :=
  ⟨⟨-23/640, -249/640⟩, 3/1280⟩
def center2834 : GaussianRat :=
  ⟨-29521383/1000000000, -142399033/500000000⟩
def contact2834 : RatBall := localContactBall tau2834 center2834
def work2834 : RoundedTauEval :=
  evalTau precision tau2834 contact2834 logTwoBall

theorem center_sq2834 : (center2834.re : ℝ)^2 +
    (center2834.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2834]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2834 : work2834.theta.ok = true ∧
    work2834.jac.invOK = true ∧ acceptsUnitSq work2834.out = true := by decide +kernel

def cell2834 : CellCertificate where
  tauBall := tau2834
  contactCenter := center2834
  contactBall := contact2834
  work := work2834
  center_sq := center_sq2834
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2834.1
  jac_ok := checks2834.2.1
  accepted := checks2834.2.2

def tau2835 : RatBall :=
  ⟨⟨-21/640, -249/640⟩, 3/1280⟩
def center2835 : GaussianRat :=
  ⟨-26958403/1000000000, -284882077/1000000000⟩
def contact2835 : RatBall := localContactBall tau2835 center2835
def work2835 : RoundedTauEval :=
  evalTau precision tau2835 contact2835 logTwoBall

theorem center_sq2835 : (center2835.re : ℝ)^2 +
    (center2835.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2835]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2835 : work2835.theta.ok = true ∧
    work2835.jac.invOK = true ∧ acceptsUnitSq work2835.out = true := by decide +kernel

def cell2835 : CellCertificate where
  tauBall := tau2835
  contactCenter := center2835
  contactBall := contact2835
  work := work2835
  center_sq := center_sq2835
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2835.1
  jac_ok := checks2835.2.1
  accepted := checks2835.2.2

def tau2836 : RatBall :=
  ⟨⟨-19/640, -251/640⟩, 3/1280⟩
def center2836 : GaussianRat :=
  ⟨-12233721/500000000, -287526937/1000000000⟩
def contact2836 : RatBall := localContactBall tau2836 center2836
def work2836 : RoundedTauEval :=
  evalTau precision tau2836 contact2836 logTwoBall

theorem center_sq2836 : (center2836.re : ℝ)^2 +
    (center2836.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2836]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2836 : work2836.theta.ok = true ∧
    work2836.jac.invOK = true ∧ acceptsUnitSq work2836.out = true := by decide +kernel

def cell2836 : CellCertificate where
  tauBall := tau2836
  contactCenter := center2836
  contactBall := contact2836
  work := work2836
  center_sq := center_sq2836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2836.1
  jac_ok := checks2836.2.1
  accepted := checks2836.2.2

def tau2837 : RatBall :=
  ⟨⟨-17/640, -251/640⟩, 3/1280⟩
def center2837 : GaussianRat :=
  ⟨-21894677/1000000000, -143798363/500000000⟩
def contact2837 : RatBall := localContactBall tau2837 center2837
def work2837 : RoundedTauEval :=
  evalTau precision tau2837 contact2837 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354


