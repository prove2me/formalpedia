-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0177
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0177
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:02.784799+00:00
-- url     : https://prove2.me/theorems/b9caba87-3b1b-4e63-afb3-b28478f35ba6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0177.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1416 : RatBall :=
  ⟨⟨-51/320, -103/320⟩, 3/640⟩
def center1416 : GaussianRat :=
  ⟨-7627513/62500000, -224552577/1000000000⟩
def contact1416 : RatBall := localContactBall tau1416 center1416
def work1416 : RoundedTauEval :=
  evalTau precision tau1416 contact1416 logTwoBall

theorem center_sq1416 : (center1416.re : ℝ)^2 +
    (center1416.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1416]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1416 : work1416.theta.ok = true ∧
    work1416.jac.invOK = true ∧ acceptsUnitSq work1416.out = true := by decide +kernel

def cell1416 : CellCertificate where
  tauBall := tau1416
  contactCenter := center1416
  contactBall := contact1416
  work := work1416
  center_sq := center_sq1416
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1416.1
  jac_ok := checks1416.2.1
  accepted := checks1416.2.2

def tau1417 : RatBall :=
  ⟨⟨-49/320, -103/320⟩, 3/640⟩
def center1417 : GaussianRat :=
  ⟨-117379261/1000000000, -56270573/250000000⟩
def contact1417 : RatBall := localContactBall tau1417 center1417
def work1417 : RoundedTauEval :=
  evalTau precision tau1417 contact1417 logTwoBall

theorem center_sq1417 : (center1417.re : ℝ)^2 +
    (center1417.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1417]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1417 : work1417.theta.ok = true ∧
    work1417.jac.invOK = true ∧ acceptsUnitSq work1417.out = true := by decide +kernel

def cell1417 : CellCertificate where
  tauBall := tau1417
  contactCenter := center1417
  contactBall := contact1417
  work := work1417
  center_sq := center_sq1417
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1417.1
  jac_ok := checks1417.2.1
  accepted := checks1417.2.2

def tau1418 : RatBall :=
  ⟨⟨-51/320, -101/320⟩, 3/640⟩
def center1418 : GaussianRat :=
  ⟨-30377187/250000000, -6872127/31250000⟩
def contact1418 : RatBall := localContactBall tau1418 center1418
def work1418 : RoundedTauEval :=
  evalTau precision tau1418 contact1418 logTwoBall

theorem center_sq1418 : (center1418.re : ℝ)^2 +
    (center1418.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1418]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1418 : work1418.theta.ok = true ∧
    work1418.jac.invOK = true ∧ acceptsUnitSq work1418.out = true := by decide +kernel

def cell1418 : CellCertificate where
  tauBall := tau1418
  contactCenter := center1418
  contactBall := contact1418
  work := work1418
  center_sq := center_sq1418
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1418.1
  jac_ok := checks1418.2.1
  accepted := checks1418.2.2

def tau1419 : RatBall :=
  ⟨⟨-49/320, -101/320⟩, 3/640⟩
def center1419 : GaussianRat :=
  ⟨-3652061/31250000, -220423219/1000000000⟩
def contact1419 : RatBall := localContactBall tau1419 center1419
def work1419 : RoundedTauEval :=
  evalTau precision tau1419 contact1419 logTwoBall

theorem center_sq1419 : (center1419.re : ℝ)^2 +
    (center1419.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1419]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1419 : work1419.theta.ok = true ∧
    work1419.jac.invOK = true ∧ acceptsUnitSq work1419.out = true := by decide +kernel

def cell1419 : CellCertificate where
  tauBall := tau1419
  contactCenter := center1419
  contactBall := contact1419
  work := work1419
  center_sq := center_sq1419
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1419.1
  jac_ok := checks1419.2.1
  accepted := checks1419.2.2

def tau1420 : RatBall :=
  ⟨⟨-47/320, -111/320⟩, 3/640⟩
def center1420 : GaussianRat :=
  ⟨-57413127/500000000, -244479579/1000000000⟩
def contact1420 : RatBall := localContactBall tau1420 center1420
def work1420 : RoundedTauEval :=
  evalTau precision tau1420 contact1420 logTwoBall

theorem center_sq1420 : (center1420.re : ℝ)^2 +
    (center1420.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1420]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1420 : work1420.theta.ok = true ∧
    work1420.jac.invOK = true ∧ acceptsUnitSq work1420.out = true := by decide +kernel

def cell1420 : CellCertificate where
  tauBall := tau1420
  contactCenter := center1420
  contactBall := contact1420
  work := work1420
  center_sq := center_sq1420
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1420.1
  jac_ok := checks1420.2.1
  accepted := checks1420.2.2

def tau1421 : RatBall :=
  ⟨⟨-9/64, -111/320⟩, 3/640⟩
def center1421 : GaussianRat :=
  ⟨-4402271/40000000, -122514671/500000000⟩
def contact1421 : RatBall := localContactBall tau1421 center1421
def work1421 : RoundedTauEval :=
  evalTau precision tau1421 contact1421 logTwoBall

theorem center_sq1421 : (center1421.re : ℝ)^2 +
    (center1421.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1421]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1421 : work1421.theta.ok = true ∧
    work1421.jac.invOK = true ∧ acceptsUnitSq work1421.out = true := by decide +kernel

def cell1421 : CellCertificate where
  tauBall := tau1421
  contactCenter := center1421
  contactBall := contact1421
  work := work1421
  center_sq := center_sq1421
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1421.1
  jac_ok := checks1421.2.1
  accepted := checks1421.2.2

def tau1422 : RatBall :=
  ⟨⟨-47/320, -109/320⟩, 3/640⟩
def center1422 : GaussianRat :=
  ⟨-3571049/31250000, -239728011/1000000000⟩
def contact1422 : RatBall := localContactBall tau1422 center1422
def work1422 : RoundedTauEval :=
  evalTau precision tau1422 contact1422 logTwoBall

theorem center_sq1422 : (center1422.re : ℝ)^2 +
    (center1422.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1422]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1422 : work1422.theta.ok = true ∧
    work1422.jac.invOK = true ∧ acceptsUnitSq work1422.out = true := by decide +kernel

def cell1422 : CellCertificate where
  tauBall := tau1422
  contactCenter := center1422
  contactBall := contact1422
  work := work1422
  center_sq := center_sq1422
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1422.1
  jac_ok := checks1422.2.1
  accepted := checks1422.2.2

def tau1423 : RatBall :=
  ⟨⟨-9/64, -109/320⟩, 3/640⟩
def center1423 : GaussianRat :=
  ⟨-109524891/1000000000, -240262931/1000000000⟩
def contact1423 : RatBall := localContactBall tau1423 center1423
def work1423 : RoundedTauEval :=
  evalTau precision tau1423 contact1423 logTwoBall

theorem center_sq1423 : (center1423.re : ℝ)^2 +
    (center1423.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1423]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1423 : work1423.theta.ok = true ∧
    work1423.jac.invOK = true ∧ acceptsUnitSq work1423.out = true := by decide +kernel

def cell1423 : CellCertificate where
  tauBall := tau1423
  contactCenter := center1423
  contactBall := contact1423
  work := work1423
  center_sq := center_sq1423
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1423.1
  jac_ok := checks1423.2.1
  accepted := checks1423.2.2

def cells : List CellCertificate := [cell1416, cell1417, cell1418, cell1419, cell1420, cell1421, cell1422, cell1423]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177

end


