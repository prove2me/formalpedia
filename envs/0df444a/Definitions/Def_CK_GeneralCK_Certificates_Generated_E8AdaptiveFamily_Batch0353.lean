-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:28.443874+00:00
-- url     : https://prove2.me/theorems/d16a0798-d6f2-4a08-a025-f8a2b6ce541d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0353.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0353_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2829 : (center2829.re : ℝ)^2 +
    (center2829.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2829]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2829 : work2829.theta.ok = true ∧
    work2829.jac.invOK = true ∧ acceptsUnitSq work2829.out = true := by decide +kernel

def cell2829 : CellCertificate where
  tauBall := tau2829
  contactCenter := center2829
  contactBall := contact2829
  work := work2829
  center_sq := center_sq2829
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2829.1
  jac_ok := checks2829.2.1
  accepted := checks2829.2.2

def tau2830 : RatBall :=
  ⟨⟨-19/640, -253/640⟩, 3/1280⟩
def center2830 : GaussianRat :=
  ⟨-24541601/1000000000, -290103079/1000000000⟩
def contact2830 : RatBall := localContactBall tau2830 center2830
def work2830 : RoundedTauEval :=
  evalTau precision tau2830 contact2830 logTwoBall

theorem center_sq2830 : (center2830.re : ℝ)^2 +
    (center2830.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2830]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2830 : work2830.theta.ok = true ∧
    work2830.jac.invOK = true ∧ acceptsUnitSq work2830.out = true := by decide +kernel

def cell2830 : CellCertificate where
  tauBall := tau2830
  contactCenter := center2830
  contactBall := contact2830
  work := work2830
  center_sq := center_sq2830
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2830.1
  jac_ok := checks2830.2.1
  accepted := checks2830.2.2

def tau2831 : RatBall :=
  ⟨⟨-17/640, -253/640⟩, 3/1280⟩
def center2831 : GaussianRat :=
  ⟨-21961069/1000000000, -145086923/500000000⟩
def contact2831 : RatBall := localContactBall tau2831 center2831
def work2831 : RoundedTauEval :=
  evalTau precision tau2831 contact2831 logTwoBall

theorem center_sq2831 : (center2831.re : ℝ)^2 +
    (center2831.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2831]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2831 : work2831.theta.ok = true ∧
    work2831.jac.invOK = true ∧ acceptsUnitSq work2831.out = true := by decide +kernel

def cell2831 : CellCertificate where
  tauBall := tau2831
  contactCenter := center2831
  contactBall := contact2831
  work := work2831
  center_sq := center_sq2831
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2831.1
  jac_ok := checks2831.2.1
  accepted := checks2831.2.2

def cells : List CellCertificate := [cell2824, cell2825, cell2826, cell2827, cell2828, cell2829, cell2830, cell2831]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353


