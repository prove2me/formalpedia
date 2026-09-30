-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:27:22.397169+00:00
-- url     : https://prove2.me/theorems/afbc401b-ce35-4a6e-9a03-56ffdc40bcf3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0139 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1115 : work1115.theta.ok = true ∧
    work1115.jac.invOK = true ∧ acceptsUnitSq work1115.out = true := by decide +kernel

def cell1115 : CellCertificate where
  tauBall := tau1115
  contactCenter := center1115
  contactBall := contact1115
  work := work1115
  center_sq := center_sq1115
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1115.1
  jac_ok := checks1115.2.1
  accepted := checks1115.2.2

def tau1116 : RatBall :=
  ⟨⟨7/160, 49/160⟩, 3/320⟩
def center1116 : GaussianRat :=
  ⟨16780473/500000000, 219087113/1000000000⟩
def contact1116 : RatBall := localContactBall tau1116 center1116
def work1116 : RoundedTauEval :=
  evalTau precision tau1116 contact1116 logTwoBall

theorem center_sq1116 : (center1116.re : ℝ)^2 +
    (center1116.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1116]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1116 : work1116.theta.ok = true ∧
    work1116.jac.invOK = true ∧ acceptsUnitSq work1116.out = true := by decide +kernel

def cell1116 : CellCertificate where
  tauBall := tau1116
  contactCenter := center1116
  contactBall := contact1116
  work := work1116
  center_sq := center_sq1116
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1116.1
  jac_ok := checks1116.2.1
  accepted := checks1116.2.2

def tau1117 : RatBall :=
  ⟨⟨1/32, 51/160⟩, 3/320⟩
def center1117 : GaussianRat :=
  ⟨24200917/1000000000, 228965453/1000000000⟩
def contact1117 : RatBall := localContactBall tau1117 center1117
def work1117 : RoundedTauEval :=
  evalTau precision tau1117 contact1117 logTwoBall

theorem center_sq1117 : (center1117.re : ℝ)^2 +
    (center1117.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1117]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1117 : work1117.theta.ok = true ∧
    work1117.jac.invOK = true ∧ acceptsUnitSq work1117.out = true := by decide +kernel

def cell1117 : CellCertificate where
  tauBall := tau1117
  contactCenter := center1117
  contactBall := contact1117
  work := work1117
  center_sq := center_sq1117
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1117.1
  jac_ok := checks1117.2.1
  accepted := checks1117.2.2

def tau1118 : RatBall :=
  ⟨⟨7/160, 51/160⟩, 3/320⟩
def center1118 : GaussianRat :=
  ⟨1693169/50000000, 228698347/1000000000⟩
def contact1118 : RatBall := localContactBall tau1118 center1118
def work1118 : RoundedTauEval :=
  evalTau precision tau1118 contact1118 logTwoBall

theorem center_sq1118 : (center1118.re : ℝ)^2 +
    (center1118.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1118 : work1118.theta.ok = true ∧
    work1118.jac.invOK = true ∧ acceptsUnitSq work1118.out = true := by decide +kernel

def cell1118 : CellCertificate where
  tauBall := tau1118
  contactCenter := center1118
  contactBall := contact1118
  work := work1118
  center_sq := center_sq1118
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1118.1
  jac_ok := checks1118.2.1
  accepted := checks1118.2.2

def tau1119 : RatBall :=
  ⟨⟨1/160, 53/160⟩, 3/320⟩
def center1119 : GaussianRat :=
  ⟨611093/125000000, 238963881/1000000000⟩
def contact1119 : RatBall := localContactBall tau1119 center1119

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139


