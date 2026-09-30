-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0043_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:14:16.462043+00:00
-- url     : https://prove2.me/theorems/ad4bebed-10ec-4155-9641-4827c0893dfc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0043 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0344 : RatBall :=
  ⟨⟨-49/160, -37/160⟩, 3/320⟩
def center0344 : GaussianRat :=
  ⟨-8639819/40000000, -36909857/250000000⟩
def contact0344 : RatBall := localContactBall tau0344 center0344
def work0344 : RoundedTauEval :=
  evalTau precision tau0344 contact0344 logTwoBall

theorem center_sq0344 : (center0344.re : ℝ)^2 +
    (center0344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0344 : work0344.theta.ok = true ∧
    work0344.jac.invOK = true ∧ acceptsUnitSq work0344.out = true := by decide +kernel

def cell0344 : CellCertificate where
  tauBall := tau0344
  contactCenter := center0344
  contactBall := contact0344
  work := work0344
  center_sq := center_sq0344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0344.1
  jac_ok := checks0344.2.1
  accepted := checks0344.2.2

def tau0345 : RatBall :=
  ⟨⟨-53/160, -33/160⟩, 3/320⟩
def center0345 : GaussianRat :=
  ⟨-114945839/500000000, -32327639/250000000⟩
def contact0345 : RatBall := localContactBall tau0345 center0345
def work0345 : RoundedTauEval :=
  evalTau precision tau0345 contact0345 logTwoBall

theorem center_sq0345 : (center0345.re : ℝ)^2 +
    (center0345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0345 : work0345.theta.ok = true ∧
    work0345.jac.invOK = true ∧ acceptsUnitSq work0345.out = true := by decide +kernel

def cell0345 : CellCertificate where
  tauBall := tau0345
  contactCenter := center0345
  contactBall := contact0345
  work := work0345
  center_sq := center_sq0345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0345.1
  jac_ok := checks0345.2.1
  accepted := checks0345.2.2

def tau0346 : RatBall :=
  ⟨⟨-51/160, -7/32⟩, 3/320⟩
def center0346 : GaussianRat :=
  ⟨-111484361/500000000, -13840239/100000000⟩
def contact0346 : RatBall := localContactBall tau0346 center0346
def work0346 : RoundedTauEval :=
  evalTau precision tau0346 contact0346 logTwoBall

theorem center_sq0346 : (center0346.re : ℝ)^2 +
    (center0346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0346 : work0346.theta.ok = true ∧
    work0346.jac.invOK = true ∧ acceptsUnitSq work0346.out = true := by decide +kernel

def cell0346 : CellCertificate where
  tauBall := tau0346
  contactCenter := center0346
  contactBall := contact0346
  work := work0346
  center_sq := center_sq0346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0346.1
  jac_ok := checks0346.2.1
  accepted := checks0346.2.2

def tau0347 : RatBall :=
  ⟨⟨-49/160, -7/32⟩, 3/320⟩
def center0347 : GaussianRat :=
  ⟨-26859619/125000000, -139498183/1000000000⟩
def contact0347 : RatBall := localContactBall tau0347 center0347
def work0347 : RoundedTauEval :=
  evalTau precision tau0347 contact0347 logTwoBall

theorem center_sq0347 : (center0347.re : ℝ)^2 +
    (center0347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0347 : work0347.theta.ok = true ∧
    work0347.jac.invOK = true ∧ acceptsUnitSq work0347.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043


