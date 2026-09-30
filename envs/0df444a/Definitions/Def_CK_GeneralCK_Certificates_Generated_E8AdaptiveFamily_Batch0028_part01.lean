-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:30.767991+00:00
-- url     : https://prove2.me/theorems/94fd3111-325a-4144-9933-208732b74d19
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0028 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center0227 : GaussianRat :=
  ⟨-163469111/1000000000, 36947527/500000000⟩
def contact0227 : RatBall := localContactBall tau0227 center0227
def work0227 : RoundedTauEval :=
  evalTau precision tau0227 contact0227 logTwoBall

theorem center_sq0227 : (center0227.re : ℝ)^2 +
    (center0227.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0227]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0227 : work0227.theta.ok = true ∧
    work0227.jac.invOK = true ∧ acceptsUnitSq work0227.out = true := by decide +kernel

def cell0227 : CellCertificate where
  tauBall := tau0227
  contactCenter := center0227
  contactBall := contact0227
  work := work0227
  center_sq := center_sq0227
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0227.1
  jac_ok := checks0227.2.1
  accepted := checks0227.2.2

def tau0228 : RatBall :=
  ⟨⟨-17/80, 9/80⟩, 3/160⟩
def center0228 : GaussianRat :=
  ⟨-29368329/200000000, 18684497/250000000⟩
def contact0228 : RatBall := localContactBall tau0228 center0228
def work0228 : RoundedTauEval :=
  evalTau precision tau0228 contact0228 logTwoBall

theorem center_sq0228 : (center0228.re : ℝ)^2 +
    (center0228.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0228]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0228 : work0228.theta.ok = true ∧
    work0228.jac.invOK = true ∧ acceptsUnitSq work0228.out = true := by decide +kernel

def cell0228 : CellCertificate where
  tauBall := tau0228
  contactCenter := center0228
  contactBall := contact0228
  work := work0228
  center_sq := center_sq0228
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0228.1
  jac_ok := checks0228.2.1
  accepted := checks0228.2.2

def tau0229 : RatBall :=
  ⟨⟨-19/80, 11/80⟩, 3/160⟩
def center0229 : GaussianRat :=
  ⟨-82225973/500000000, 18092371/200000000⟩
def contact0229 : RatBall := localContactBall tau0229 center0229
def work0229 : RoundedTauEval :=
  evalTau precision tau0229 contact0229 logTwoBall

theorem center_sq0229 : (center0229.re : ℝ)^2 +
    (center0229.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0229]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0229 : work0229.theta.ok = true ∧
    work0229.jac.invOK = true ∧ acceptsUnitSq work0229.out = true := by decide +kernel

def cell0229 : CellCertificate where
  tauBall := tau0229
  contactCenter := center0229
  contactBall := contact0229
  work := work0229
  center_sq := center_sq0229
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0229.1
  jac_ok := checks0229.2.1
  accepted := checks0229.2.2

def tau0230 : RatBall :=
  ⟨⟨-17/80, 11/80⟩, 3/160⟩
def center0230 : GaussianRat :=
  ⟨-1154229/7812500, 91503559/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028


