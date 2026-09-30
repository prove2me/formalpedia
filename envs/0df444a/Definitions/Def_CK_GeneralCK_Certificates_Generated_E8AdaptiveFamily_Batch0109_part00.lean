-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0109_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:09.568773+00:00
-- url     : https://prove2.me/theorems/122e4b43-e376-456f-b30d-8234640aee75
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0109 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0872 : RatBall :=
  ⟨⟨-39/160, 7/32⟩, 3/320⟩
def center0872 : GaussianRat :=
  ⟨-173384937/1000000000, 144541281/1000000000⟩
def contact0872 : RatBall := localContactBall tau0872 center0872
def work0872 : RoundedTauEval :=
  evalTau precision tau0872 contact0872 logTwoBall

theorem center_sq0872 : (center0872.re : ℝ)^2 +
    (center0872.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0872]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0872 : work0872.theta.ok = true ∧
    work0872.jac.invOK = true ∧ acceptsUnitSq work0872.out = true := by decide +kernel

def cell0872 : CellCertificate where
  tauBall := tau0872
  contactCenter := center0872
  contactBall := contact0872
  work := work0872
  center_sq := center_sq0872
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0872.1
  jac_ok := checks0872.2.1
  accepted := checks0872.2.2

def tau0873 : RatBall :=
  ⟨⟨-37/160, 7/32⟩, 3/320⟩
def center0873 : GaussianRat :=
  ⟨-164892819/1000000000, 29090197/200000000⟩
def contact0873 : RatBall := localContactBall tau0873 center0873
def work0873 : RoundedTauEval :=
  evalTau precision tau0873 contact0873 logTwoBall

theorem center_sq0873 : (center0873.re : ℝ)^2 +
    (center0873.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0873]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0873 : work0873.theta.ok = true ∧
    work0873.jac.invOK = true ∧ acceptsUnitSq work0873.out = true := by decide +kernel

def cell0873 : CellCertificate where
  tauBall := tau0873
  contactCenter := center0873
  contactBall := contact0873
  work := work0873
  center_sq := center_sq0873
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0873.1
  jac_ok := checks0873.2.1
  accepted := checks0873.2.2

def tau0874 : RatBall :=
  ⟨⟨-7/32, 33/160⟩, 3/320⟩
def center0874 : GaussianRat :=
  ⟨-31103099/200000000, 137761833/1000000000⟩
def contact0874 : RatBall := localContactBall tau0874 center0874
def work0874 : RoundedTauEval :=
  evalTau precision tau0874 contact0874 logTwoBall

theorem center_sq0874 : (center0874.re : ℝ)^2 +
    (center0874.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0874]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0874 : work0874.theta.ok = true ∧
    work0874.jac.invOK = true ∧ acceptsUnitSq work0874.out = true := by decide +kernel

def cell0874 : CellCertificate where
  tauBall := tau0874
  contactCenter := center0874
  contactBall := contact0874
  work := work0874
  center_sq := center_sq0874
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0874.1
  jac_ok := checks0874.2.1
  accepted := checks0874.2.2

def tau0875 : RatBall :=
  ⟨⟨-33/160, 33/160⟩, 3/320⟩
def center0875 : GaussianRat :=
  ⟨-73472183/500000000, 69270487/500000000⟩
def contact0875 : RatBall := localContactBall tau0875 center0875
def work0875 : RoundedTauEval :=
  evalTau precision tau0875 contact0875 logTwoBall

theorem center_sq0875 : (center0875.re : ℝ)^2 +
    (center0875.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0875]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109


