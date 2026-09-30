-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0359_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0359_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:39.787593+00:00
-- url     : https://prove2.me/theorems/8908e356-8fa4-40c5-aa7e-705cb84931f0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0359 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2872 : RatBall :=
  ⟨⟨-3/640, -51/128⟩, 3/1280⟩
def center2872 : GaussianRat :=
  ⟨-3889311/1000000000, -293038261/1000000000⟩
def contact2872 : RatBall := localContactBall tau2872 center2872
def work2872 : RoundedTauEval :=
  evalTau precision tau2872 contact2872 logTwoBall

theorem center_sq2872 : (center2872.re : ℝ)^2 +
    (center2872.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2872]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2872 : work2872.theta.ok = true ∧
    work2872.jac.invOK = true ∧ acceptsUnitSq work2872.out = true := by decide +kernel

def cell2872 : CellCertificate where
  tauBall := tau2872
  contactCenter := center2872
  contactBall := contact2872
  work := work2872
  center_sq := center_sq2872
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2872.1
  jac_ok := checks2872.2.1
  accepted := checks2872.2.2

def tau2873 : RatBall :=
  ⟨⟨-1/640, -51/128⟩, 3/1280⟩
def center2873 : GaussianRat :=
  ⟨-162057/125000000, -58609251/200000000⟩
def contact2873 : RatBall := localContactBall tau2873 center2873
def work2873 : RoundedTauEval :=
  evalTau precision tau2873 contact2873 logTwoBall

theorem center_sq2873 : (center2873.re : ℝ)^2 +
    (center2873.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2873]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2873 : work2873.theta.ok = true ∧
    work2873.jac.invOK = true ∧ acceptsUnitSq work2873.out = true := by decide +kernel

def cell2873 : CellCertificate where
  tauBall := tau2873
  contactCenter := center2873
  contactBall := contact2873
  work := work2873
  center_sq := center_sq2873
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2873.1
  jac_ok := checks2873.2.1
  accepted := checks2873.2.2

def tau2874 : RatBall :=
  ⟨⟨-3/640, -253/640⟩, 3/1280⟩
def center2874 : GaussianRat :=
  ⟨-3877403/1000000000, -36306181/125000000⟩
def contact2874 : RatBall := localContactBall tau2874 center2874
def work2874 : RoundedTauEval :=
  evalTau precision tau2874 contact2874 logTwoBall

theorem center_sq2874 : (center2874.re : ℝ)^2 +
    (center2874.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2874]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2874 : work2874.theta.ok = true ∧
    work2874.jac.invOK = true ∧ acceptsUnitSq work2874.out = true := by decide +kernel

def cell2874 : CellCertificate where
  tauBall := tau2874
  contactCenter := center2874
  contactBall := contact2874
  work := work2874
  center_sq := center_sq2874
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2874.1
  jac_ok := checks2874.2.1
  accepted := checks2874.2.2

def tau2875 : RatBall :=
  ⟨⟨-1/640, -253/640⟩, 3/1280⟩
def center2875 : GaussianRat :=
  ⟨-646243/500000000, -72614333/250000000⟩
def contact2875 : RatBall := localContactBall tau2875 center2875
def work2875 : RoundedTauEval :=
  evalTau precision tau2875 contact2875 logTwoBall

theorem center_sq2875 : (center2875.re : ℝ)^2 +
    (center2875.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2875]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2875 : work2875.theta.ok = true ∧
    work2875.jac.invOK = true ∧ acceptsUnitSq work2875.out = true := by decide +kernel

def cell2875 : CellCertificate where
  tauBall := tau2875
  contactCenter := center2875
  contactBall := contact2875
  work := work2875
  center_sq := center_sq2875
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2875.1
  jac_ok := checks2875.2.1
  accepted := checks2875.2.2

def tau2876 : RatBall :=
  ⟨⟨-7/640, -251/640⟩, 3/1280⟩
def center2876 : GaussianRat :=
  ⟨-9019241/1000000000, -287829653/1000000000⟩
def contact2876 : RatBall := localContactBall tau2876 center2876
def work2876 : RoundedTauEval :=
  evalTau precision tau2876 contact2876 logTwoBall

theorem center_sq2876 : (center2876.re : ℝ)^2 +
    (center2876.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2876]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2876 : work2876.theta.ok = true ∧
    work2876.jac.invOK = true ∧ acceptsUnitSq work2876.out = true := by decide +kernel

def cell2876 : CellCertificate where
  tauBall := tau2876
  contactCenter := center2876
  contactBall := contact2876
  work := work2876
  center_sq := center_sq2876
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2876.1
  jac_ok := checks2876.2.1
  accepted := checks2876.2.2

def tau2877 : RatBall :=
  ⟨⟨-1/128, -251/640⟩, 3/1280⟩
def center2877 : GaussianRat :=
  ⟨-3221293/500000000, -287852971/1000000000⟩
def contact2877 : RatBall := localContactBall tau2877 center2877

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359


