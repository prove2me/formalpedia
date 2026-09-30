-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0055_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:09.318785+00:00
-- url     : https://prove2.me/theorems/85eb31b2-81b5-4f8b-b61f-15a7c12d9095
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0055 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0440 : RatBall :=
  ⟨⟨-5/32, -9/32⟩, 3/320⟩
def center0440 : GaussianRat :=
  ⟨-116565793/1000000000, -194890619/1000000000⟩
def contact0440 : RatBall := localContactBall tau0440 center0440
def work0440 : RoundedTauEval :=
  evalTau precision tau0440 contact0440 logTwoBall

theorem center_sq0440 : (center0440.re : ℝ)^2 +
    (center0440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0440 : work0440.theta.ok = true ∧
    work0440.jac.invOK = true ∧ acceptsUnitSq work0440.out = true := by decide +kernel

def cell0440 : CellCertificate where
  tauBall := tau0440
  contactCenter := center0440
  contactBall := contact0440
  work := work0440
  center_sq := center_sq0440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0440.1
  jac_ok := checks0440.2.1
  accepted := checks0440.2.2

def tau0441 : RatBall :=
  ⟨⟨-31/160, -43/160⟩, 3/320⟩
def center0441 : GaussianRat :=
  ⟨-71299541/500000000, -91537843/500000000⟩
def contact0441 : RatBall := localContactBall tau0441 center0441
def work0441 : RoundedTauEval :=
  evalTau precision tau0441 contact0441 logTwoBall

theorem center_sq0441 : (center0441.re : ℝ)^2 +
    (center0441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0441 : work0441.theta.ok = true ∧
    work0441.jac.invOK = true ∧ acceptsUnitSq work0441.out = true := by decide +kernel

def cell0441 : CellCertificate where
  tauBall := tau0441
  contactCenter := center0441
  contactBall := contact0441
  work := work0441
  center_sq := center_sq0441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0441.1
  jac_ok := checks0441.2.1
  accepted := checks0441.2.2

def tau0442 : RatBall :=
  ⟨⟨-29/160, -43/160⟩, 3/320⟩
def center0442 : GaussianRat :=
  ⟨-66845797/500000000, -18404523/100000000⟩
def contact0442 : RatBall := localContactBall tau0442 center0442
def work0442 : RoundedTauEval :=
  evalTau precision tau0442 contact0442 logTwoBall

theorem center_sq0442 : (center0442.re : ℝ)^2 +
    (center0442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0442 : work0442.theta.ok = true ∧
    work0442.jac.invOK = true ∧ acceptsUnitSq work0442.out = true := by decide +kernel

def cell0442 : CellCertificate where
  tauBall := tau0442
  contactCenter := center0442
  contactBall := contact0442
  work := work0442
  center_sq := center_sq0442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0442.1
  jac_ok := checks0442.2.1
  accepted := checks0442.2.2

def tau0443 : RatBall :=
  ⟨⟨-31/160, -41/160⟩, 3/320⟩
def center0443 : GaussianRat :=
  ⟨-8852011/62500000, -87111573/500000000⟩
def contact0443 : RatBall := localContactBall tau0443 center0443
def work0443 : RoundedTauEval :=
  evalTau precision tau0443 contact0443 logTwoBall

theorem center_sq0443 : (center0443.re : ℝ)^2 +
    (center0443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0443]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055


