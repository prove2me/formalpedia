-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:20.380264+00:00
-- url     : https://prove2.me/theorems/96f0a5f7-ffa0-4716-b08f-7716e441e9df
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0135 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1080 : RatBall :=
  ⟨⟨19/160, 41/160⟩, 3/320⟩
def center1080 : GaussianRat :=
  ⟨43873979/500000000, 35778323/200000000⟩
def contact1080 : RatBall := localContactBall tau1080 center1080
def work1080 : RoundedTauEval :=
  evalTau precision tau1080 contact1080 logTwoBall

theorem center_sq1080 : (center1080.re : ℝ)^2 +
    (center1080.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1080]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1080 : work1080.theta.ok = true ∧
    work1080.jac.invOK = true ∧ acceptsUnitSq work1080.out = true := by decide +kernel

def cell1080 : CellCertificate where
  tauBall := tau1080
  contactCenter := center1080
  contactBall := contact1080
  work := work1080
  center_sq := center_sq1080
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1080.1
  jac_ok := checks1080.2.1
  accepted := checks1080.2.2

def tau1081 : RatBall :=
  ⟨⟨17/160, 43/160⟩, 3/320⟩
def center1081 : GaussianRat :=
  ⟨39590143/500000000, 47162917/250000000⟩
def contact1081 : RatBall := localContactBall tau1081 center1081
def work1081 : RoundedTauEval :=
  evalTau precision tau1081 contact1081 logTwoBall

theorem center_sq1081 : (center1081.re : ℝ)^2 +
    (center1081.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1081]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1081 : work1081.theta.ok = true ∧
    work1081.jac.invOK = true ∧ acceptsUnitSq work1081.out = true := by decide +kernel

def cell1081 : CellCertificate where
  tauBall := tau1081
  contactCenter := center1081
  contactBall := contact1081
  work := work1081
  center_sq := center_sq1081
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1081.1
  jac_ok := checks1081.2.1
  accepted := checks1081.2.2

def tau1082 : RatBall :=
  ⟨⟨19/160, 43/160⟩, 3/320⟩
def center1082 : GaussianRat :=
  ⟨88375401/1000000000, 188036739/1000000000⟩
def contact1082 : RatBall := localContactBall tau1082 center1082
def work1082 : RoundedTauEval :=
  evalTau precision tau1082 contact1082 logTwoBall

theorem center_sq1082 : (center1082.re : ℝ)^2 +
    (center1082.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1082]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1082 : work1082.theta.ok = true ∧
    work1082.jac.invOK = true ∧ acceptsUnitSq work1082.out = true := by decide +kernel

def cell1082 : CellCertificate where
  tauBall := tau1082
  contactCenter := center1082
  contactBall := contact1082
  work := work1082
  center_sq := center_sq1082
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1082.1
  jac_ok := checks1082.2.1
  accepted := checks1082.2.2

def tau1083 : RatBall :=
  ⟨⟨21/160, 41/160⟩, 3/320⟩
def center1083 : GaussianRat :=
  ⟨96843181/1000000000, 5570429/31250000⟩
def contact1083 : RatBall := localContactBall tau1083 center1083
def work1083 : RoundedTauEval :=
  evalTau precision tau1083 contact1083 logTwoBall

theorem center_sq1083 : (center1083.re : ℝ)^2 +
    (center1083.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1083]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1083 : work1083.theta.ok = true ∧
    work1083.jac.invOK = true ∧ acceptsUnitSq work1083.out = true := by decide +kernel

def cell1083 : CellCertificate where
  tauBall := tau1083
  contactCenter := center1083
  contactBall := contact1083
  work := work1083
  center_sq := center_sq1083
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1083.1
  jac_ok := checks1083.2.1
  accepted := checks1083.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135


