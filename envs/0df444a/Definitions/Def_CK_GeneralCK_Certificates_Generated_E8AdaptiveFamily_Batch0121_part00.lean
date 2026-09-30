-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0121_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:11:23.390138+00:00
-- url     : https://prove2.me/theorems/1394d055-0e7f-4bcc-8311-e84ed9bbc4ac
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0121 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0968 : RatBall :=
  ⟨⟨-9/160, 11/32⟩, 3/320⟩
def center0968 : GaussianRat :=
  ⟨-44352537/1000000000, 61948059/250000000⟩
def contact0968 : RatBall := localContactBall tau0968 center0968
def work0968 : RoundedTauEval :=
  evalTau precision tau0968 contact0968 logTwoBall

theorem center_sq0968 : (center0968.re : ℝ)^2 +
    (center0968.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0968]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0968 : work0968.theta.ok = true ∧
    work0968.jac.invOK = true ∧ acceptsUnitSq work0968.out = true := by decide +kernel

def cell0968 : CellCertificate where
  tauBall := tau0968
  contactCenter := center0968
  contactBall := contact0968
  work := work0968
  center_sq := center_sq0968
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0968.1
  jac_ok := checks0968.2.1
  accepted := checks0968.2.2

def tau0969 : RatBall :=
  ⟨⟨-7/160, 49/160⟩, 3/320⟩
def center0969 : GaussianRat :=
  ⟨-16780473/500000000, 219087113/1000000000⟩
def contact0969 : RatBall := localContactBall tau0969 center0969
def work0969 : RoundedTauEval :=
  evalTau precision tau0969 contact0969 logTwoBall

theorem center_sq0969 : (center0969.re : ℝ)^2 +
    (center0969.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0969]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0969 : work0969.theta.ok = true ∧
    work0969.jac.invOK = true ∧ acceptsUnitSq work0969.out = true := by decide +kernel

def cell0969 : CellCertificate where
  tauBall := tau0969
  contactCenter := center0969
  contactBall := contact0969
  work := work0969
  center_sq := center_sq0969
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0969.1
  jac_ok := checks0969.2.1
  accepted := checks0969.2.2

def tau0970 : RatBall :=
  ⟨⟨-1/32, 49/160⟩, 3/320⟩
def center0970 : GaussianRat :=
  ⟨-2398433/100000000, 219339251/1000000000⟩
def contact0970 : RatBall := localContactBall tau0970 center0970
def work0970 : RoundedTauEval :=
  evalTau precision tau0970 contact0970 logTwoBall

theorem center_sq0970 : (center0970.re : ℝ)^2 +
    (center0970.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0970]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0970 : work0970.theta.ok = true ∧
    work0970.jac.invOK = true ∧ acceptsUnitSq work0970.out = true := by decide +kernel

def cell0970 : CellCertificate where
  tauBall := tau0970
  contactCenter := center0970
  contactBall := contact0970
  work := work0970
  center_sq := center_sq0970
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0970.1
  jac_ok := checks0970.2.1
  accepted := checks0970.2.2

def tau0971 : RatBall :=
  ⟨⟨-7/160, 51/160⟩, 3/320⟩
def center0971 : GaussianRat :=
  ⟨-1693169/50000000, 228698347/1000000000⟩
def contact0971 : RatBall := localContactBall tau0971 center0971
def work0971 : RoundedTauEval :=
  evalTau precision tau0971 contact0971 logTwoBall

theorem center_sq0971 : (center0971.re : ℝ)^2 +
    (center0971.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0971]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121


