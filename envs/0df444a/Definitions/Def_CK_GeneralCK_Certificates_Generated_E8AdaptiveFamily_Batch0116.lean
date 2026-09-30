-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:59:37.056659+00:00
-- url     : https://prove2.me/theorems/69d690fb-84e7-4ccf-9b01-b216a52d7caf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0116.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0932 : (center0932.re : ℝ)^2 +
    (center0932.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0932]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0932 : work0932.theta.ok = true ∧
    work0932.jac.invOK = true ∧ acceptsUnitSq work0932.out = true := by decide +kernel

def cell0932 : CellCertificate where
  tauBall := tau0932
  contactCenter := center0932
  contactBall := contact0932
  work := work0932
  center_sq := center_sq0932
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0932.1
  jac_ok := checks0932.2.1
  accepted := checks0932.2.2

def tau0933 : RatBall :=
  ⟨⟨-21/160, 47/160⟩, 3/320⟩
def center0933 : GaussianRat :=
  ⟨-618987/6250000, 102878573/500000000⟩
def contact0933 : RatBall := localContactBall tau0933 center0933
def work0933 : RoundedTauEval :=
  evalTau precision tau0933 contact0933 logTwoBall

theorem center_sq0933 : (center0933.re : ℝ)^2 +
    (center0933.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0933]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0933 : work0933.theta.ok = true ∧
    work0933.jac.invOK = true ∧ acceptsUnitSq work0933.out = true := by decide +kernel

def cell0933 : CellCertificate where
  tauBall := tau0933
  contactCenter := center0933
  contactBall := contact0933
  work := work0933
  center_sq := center_sq0933
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0933.1
  jac_ok := checks0933.2.1
  accepted := checks0933.2.2

def tau0934 : RatBall :=
  ⟨⟨-19/160, 9/32⟩, 3/320⟩
def center0934 : GaussianRat :=
  ⟨-22260513/250000000, 49311287/250000000⟩
def contact0934 : RatBall := localContactBall tau0934 center0934
def work0934 : RoundedTauEval :=
  evalTau precision tau0934 contact0934 logTwoBall

theorem center_sq0934 : (center0934.re : ℝ)^2 +
    (center0934.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0934]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0934 : work0934.theta.ok = true ∧
    work0934.jac.invOK = true ∧ acceptsUnitSq work0934.out = true := by decide +kernel

def cell0934 : CellCertificate where
  tauBall := tau0934
  contactCenter := center0934
  contactBall := contact0934
  work := work0934
  center_sq := center_sq0934
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0934.1
  jac_ok := checks0934.2.1
  accepted := checks0934.2.2

def tau0935 : RatBall :=
  ⟨⟨-17/160, 9/32⟩, 3/320⟩
def center0935 : GaussianRat :=
  ⟨-19945259/250000000, 39579621/200000000⟩
def contact0935 : RatBall := localContactBall tau0935 center0935
def work0935 : RoundedTauEval :=
  evalTau precision tau0935 contact0935 logTwoBall

theorem center_sq0935 : (center0935.re : ℝ)^2 +
    (center0935.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0935]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0935 : work0935.theta.ok = true ∧
    work0935.jac.invOK = true ∧ acceptsUnitSq work0935.out = true := by decide +kernel

def cell0935 : CellCertificate where
  tauBall := tau0935
  contactCenter := center0935
  contactBall := contact0935
  work := work0935
  center_sq := center_sq0935
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0935.1
  jac_ok := checks0935.2.1
  accepted := checks0935.2.2

def cells : List CellCertificate := [cell0928, cell0929, cell0930, cell0931, cell0932, cell0933, cell0934, cell0935]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116


