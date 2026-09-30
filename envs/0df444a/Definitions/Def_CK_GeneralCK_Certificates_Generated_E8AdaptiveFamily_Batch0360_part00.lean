-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0360_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:22:29.567013+00:00
-- url     : https://prove2.me/theorems/40ed9e30-e075-4105-9138-1804ab2db46b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0360 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2880 : RatBall :=
  ⟨⟨-3/640, -251/640⟩, 3/1280⟩
def center2880 : GaussianRat :=
  ⟨-193283/50000000, -143934259/500000000⟩
def contact2880 : RatBall := localContactBall tau2880 center2880
def work2880 : RoundedTauEval :=
  evalTau precision tau2880 contact2880 logTwoBall

theorem center_sq2880 : (center2880.re : ℝ)^2 +
    (center2880.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2880]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2880 : work2880.theta.ok = true ∧
    work2880.jac.invOK = true ∧ acceptsUnitSq work2880.out = true := by decide +kernel

def cell2880 : CellCertificate where
  tauBall := tau2880
  contactCenter := center2880
  contactBall := contact2880
  work := work2880
  center_sq := center_sq2880
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2880.1
  jac_ok := checks2880.2.1
  accepted := checks2880.2.2

def tau2881 : RatBall :=
  ⟨⟨-1/640, -251/640⟩, 3/1280⟩
def center2881 : GaussianRat :=
  ⟨-1288571/1000000000, -287876293/1000000000⟩
def contact2881 : RatBall := localContactBall tau2881 center2881
def work2881 : RoundedTauEval :=
  evalTau precision tau2881 contact2881 logTwoBall

theorem center_sq2881 : (center2881.re : ℝ)^2 +
    (center2881.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2881]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2881 : work2881.theta.ok = true ∧
    work2881.jac.invOK = true ∧ acceptsUnitSq work2881.out = true := by decide +kernel

def cell2881 : CellCertificate where
  tauBall := tau2881
  contactCenter := center2881
  contactBall := contact2881
  work := work2881
  center_sq := center_sq2881
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2881.1
  jac_ok := checks2881.2.1
  accepted := checks2881.2.2

def tau2882 : RatBall :=
  ⟨⟨-3/640, -249/640⟩, 3/1280⟩
def center2882 : GaussianRat :=
  ⟨-3854079/1000000000, -142647681/500000000⟩
def contact2882 : RatBall := localContactBall tau2882 center2882
def work2882 : RoundedTauEval :=
  evalTau precision tau2882 contact2882 logTwoBall

theorem center_sq2882 : (center2882.re : ℝ)^2 +
    (center2882.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2882]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2882 : work2882.theta.ok = true ∧
    work2882.jac.invOK = true ∧ acceptsUnitSq work2882.out = true := by decide +kernel

def cell2882 : CellCertificate where
  tauBall := tau2882
  contactCenter := center2882
  contactBall := contact2882
  work := work2882
  center_sq := center_sq2882
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2882.1
  jac_ok := checks2882.2.1
  accepted := checks2882.2.2

def tau2883 : RatBall :=
  ⟨⟨-1/640, -249/640⟩, 3/1280⟩
def center2883 : GaussianRat :=
  ⟨-1284711/1000000000, -285303029/1000000000⟩
def contact2883 : RatBall := localContactBall tau2883 center2883
def work2883 : RoundedTauEval :=
  evalTau precision tau2883 contact2883 logTwoBall

theorem center_sq2883 : (center2883.re : ℝ)^2 +
    (center2883.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2883]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2883 : work2883.theta.ok = true ∧
    work2883.jac.invOK = true ∧ acceptsUnitSq work2883.out = true := by decide +kernel

def cell2883 : CellCertificate where
  tauBall := tau2883
  contactCenter := center2883
  contactBall := contact2883
  work := work2883
  center_sq := center_sq2883
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2883.1
  jac_ok := checks2883.2.1
  accepted := checks2883.2.2

def tau2884 : RatBall :=
  ⟨⟨1/640, -51/128⟩, 3/1280⟩
def center2884 : GaussianRat :=
  ⟨162057/125000000, -58609251/200000000⟩
def contact2884 : RatBall := localContactBall tau2884 center2884
def work2884 : RoundedTauEval :=
  evalTau precision tau2884 contact2884 logTwoBall

theorem center_sq2884 : (center2884.re : ℝ)^2 +
    (center2884.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2884]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2884 : work2884.theta.ok = true ∧
    work2884.jac.invOK = true ∧ acceptsUnitSq work2884.out = true := by decide +kernel

def cell2884 : CellCertificate where
  tauBall := tau2884
  contactCenter := center2884
  contactBall := contact2884
  work := work2884
  center_sq := center_sq2884
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2884.1
  jac_ok := checks2884.2.1
  accepted := checks2884.2.2

def tau2885 : RatBall :=
  ⟨⟨3/640, -51/128⟩, 3/1280⟩
def center2885 : GaussianRat :=
  ⟨3889311/1000000000, -293038261/1000000000⟩
def contact2885 : RatBall := localContactBall tau2885 center2885

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360


