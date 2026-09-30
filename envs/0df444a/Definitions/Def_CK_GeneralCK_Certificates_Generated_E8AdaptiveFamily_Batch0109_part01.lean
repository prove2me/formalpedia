-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:04:47.072909+00:00
-- url     : https://prove2.me/theorems/31be6052-97d5-471e-a5bd-b2454cc004a0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0109 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0875 : work0875.theta.ok = true ∧
    work0875.jac.invOK = true ∧ acceptsUnitSq work0875.out = true := by decide +kernel

def cell0875 : CellCertificate where
  tauBall := tau0875
  contactCenter := center0875
  contactBall := contact0875
  work := work0875
  center_sq := center_sq0875
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0875.1
  jac_ok := checks0875.2.1
  accepted := checks0875.2.2

def tau0876 : RatBall :=
  ⟨⟨-7/32, 7/32⟩, 3/320⟩
def center0876 : GaussianRat :=
  ⟨-78170517/500000000, 14632387/100000000⟩
def contact0876 : RatBall := localContactBall tau0876 center0876
def work0876 : RoundedTauEval :=
  evalTau precision tau0876 contact0876 logTwoBall

theorem center_sq0876 : (center0876.re : ℝ)^2 +
    (center0876.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0876]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0876 : work0876.theta.ok = true ∧
    work0876.jac.invOK = true ∧ acceptsUnitSq work0876.out = true := by decide +kernel

def cell0876 : CellCertificate where
  tauBall := tau0876
  contactCenter := center0876
  contactBall := contact0876
  work := work0876
  center_sq := center_sq0876
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0876.1
  jac_ok := checks0876.2.1
  accepted := checks0876.2.2

def tau0877 : RatBall :=
  ⟨⟨-33/160, 7/32⟩, 3/320⟩
def center0877 : GaussianRat :=
  ⟨-7386597/50000000, 7357917/50000000⟩
def contact0877 : RatBall := localContactBall tau0877 center0877
def work0877 : RoundedTauEval :=
  evalTau precision tau0877 contact0877 logTwoBall

theorem center_sq0877 : (center0877.re : ℝ)^2 +
    (center0877.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0877]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0877 : work0877.theta.ok = true ∧
    work0877.jac.invOK = true ∧ acceptsUnitSq work0877.out = true := by decide +kernel

def cell0877 : CellCertificate where
  tauBall := tau0877
  contactCenter := center0877
  contactBall := contact0877
  work := work0877
  center_sq := center_sq0877
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0877.1
  jac_ok := checks0877.2.1
  accepted := checks0877.2.2

def tau0878 : RatBall :=
  ⟨⟨-39/160, 37/160⟩, 3/320⟩
def center0878 : GaussianRat :=
  ⟨-174343743/1000000000, 153020771/1000000000⟩
def contact0878 : RatBall := localContactBall tau0878 center0878
def work0878 : RoundedTauEval :=
  evalTau precision tau0878 contact0878 logTwoBall

theorem center_sq0878 : (center0878.re : ℝ)^2 +
    (center0878.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0878]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0878 : work0878.theta.ok = true ∧
    work0878.jac.invOK = true ∧ acceptsUnitSq work0878.out = true := by decide +kernel

def cell0878 : CellCertificate where
  tauBall := tau0878
  contactCenter := center0878
  contactBall := contact0878
  work := work0878
  center_sq := center_sq0878
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0878.1
  jac_ok := checks0878.2.1
  accepted := checks0878.2.2

def tau0879 : RatBall :=
  ⟨⟨-37/160, 37/160⟩, 3/320⟩
def center0879 : GaussianRat :=
  ⟨-33162899/200000000, 153992113/1000000000⟩
def contact0879 : RatBall := localContactBall tau0879 center0879

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109


