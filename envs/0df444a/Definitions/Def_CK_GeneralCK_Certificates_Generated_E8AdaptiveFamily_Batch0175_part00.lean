-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0175_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:17:37.798291+00:00
-- url     : https://prove2.me/theorems/e9a8b937-ebab-4d29-a95b-ffa00acccdc3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0175 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1400 : RatBall :=
  ⟨⟨-59/320, -103/320⟩, 3/640⟩
def center1400 : GaussianRat :=
  ⟨-140529903/1000000000, -222254637/1000000000⟩
def contact1400 : RatBall := localContactBall tau1400 center1400
def work1400 : RoundedTauEval :=
  evalTau precision tau1400 contact1400 logTwoBall

theorem center_sq1400 : (center1400.re : ℝ)^2 +
    (center1400.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1400]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1400 : work1400.theta.ok = true ∧
    work1400.jac.invOK = true ∧ acceptsUnitSq work1400.out = true := by decide +kernel

def cell1400 : CellCertificate where
  tauBall := tau1400
  contactCenter := center1400
  contactBall := contact1400
  work := work1400
  center_sq := center_sq1400
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1400.1
  jac_ok := checks1400.2.1
  accepted := checks1400.2.2

def tau1401 : RatBall :=
  ⟨⟨-57/320, -103/320⟩, 3/640⟩
def center1401 : GaussianRat :=
  ⟨-135931497/1000000000, -55713833/250000000⟩
def contact1401 : RatBall := localContactBall tau1401 center1401
def work1401 : RoundedTauEval :=
  evalTau precision tau1401 contact1401 logTwoBall

theorem center_sq1401 : (center1401.re : ℝ)^2 +
    (center1401.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1401]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1401 : work1401.theta.ok = true ∧
    work1401.jac.invOK = true ∧ acceptsUnitSq work1401.out = true := by decide +kernel

def cell1401 : CellCertificate where
  tauBall := tau1401
  contactCenter := center1401
  contactBall := contact1401
  work := work1401
  center_sq := center_sq1401
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1401.1
  jac_ok := checks1401.2.1
  accepted := checks1401.2.2

def tau1402 : RatBall :=
  ⟨⟨-59/320, -101/320⟩, 3/640⟩
def center1402 : GaussianRat :=
  ⟨-27985801/200000000, -54418229/250000000⟩
def contact1402 : RatBall := localContactBall tau1402 center1402
def work1402 : RoundedTauEval :=
  evalTau precision tau1402 contact1402 logTwoBall

theorem center_sq1402 : (center1402.re : ℝ)^2 +
    (center1402.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1402]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1402 : work1402.theta.ok = true ∧
    work1402.jac.invOK = true ∧ acceptsUnitSq work1402.out = true := by decide +kernel

def cell1402 : CellCertificate where
  tauBall := tau1402
  contactCenter := center1402
  contactBall := contact1402
  work := work1402
  center_sq := center_sq1402
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1402.1
  jac_ok := checks1402.2.1
  accepted := checks1402.2.2

def tau1403 : RatBall :=
  ⟨⟨-57/320, -101/320⟩, 3/640⟩
def center1403 : GaussianRat :=
  ⟨-135347471/1000000000, -43651451/200000000⟩
def contact1403 : RatBall := localContactBall tau1403 center1403
def work1403 : RoundedTauEval :=
  evalTau precision tau1403 contact1403 logTwoBall

theorem center_sq1403 : (center1403.re : ℝ)^2 +
    (center1403.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1403]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1403 : work1403.theta.ok = true ∧
    work1403.jac.invOK = true ∧ acceptsUnitSq work1403.out = true := by decide +kernel

def cell1403 : CellCertificate where
  tauBall := tau1403
  contactCenter := center1403
  contactBall := contact1403
  work := work1403
  center_sq := center_sq1403
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1403.1
  jac_ok := checks1403.2.1
  accepted := checks1403.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175


