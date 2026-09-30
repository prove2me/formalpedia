-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:52:55.738824+00:00
-- url     : https://prove2.me/theorems/f10e4077-1329-471c-b2b1-0681e163e97a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0168 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1344 : RatBall :=
  ⟨⟨-53/320, -113/320⟩, 3/640⟩
def center1344 : GaussianRat :=
  ⟨-129670733/1000000000, -15464381/62500000⟩
def contact1344 : RatBall := localContactBall tau1344 center1344
def work1344 : RoundedTauEval :=
  evalTau precision tau1344 contact1344 logTwoBall

theorem center_sq1344 : (center1344.re : ℝ)^2 +
    (center1344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1344 : work1344.theta.ok = true ∧
    work1344.jac.invOK = true ∧ acceptsUnitSq work1344.out = true := by decide +kernel

def cell1344 : CellCertificate where
  tauBall := tau1344
  contactCenter := center1344
  contactBall := contact1344
  work := work1344
  center_sq := center_sq1344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1344.1
  jac_ok := checks1344.2.1
  accepted := checks1344.2.2

def tau1345 : RatBall :=
  ⟨⟨-51/320, -113/320⟩, 3/640⟩
def center1345 : GaussianRat :=
  ⟨-124928411/1000000000, -12402911/50000000⟩
def contact1345 : RatBall := localContactBall tau1345 center1345
def work1345 : RoundedTauEval :=
  evalTau precision tau1345 contact1345 logTwoBall

theorem center_sq1345 : (center1345.re : ℝ)^2 +
    (center1345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1345 : work1345.theta.ok = true ∧
    work1345.jac.invOK = true ∧ acceptsUnitSq work1345.out = true := by decide +kernel

def cell1345 : CellCertificate where
  tauBall := tau1345
  contactCenter := center1345
  contactBall := contact1345
  work := work1345
  center_sq := center_sq1345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1345.1
  jac_ok := checks1345.2.1
  accepted := checks1345.2.2

def tau1346 : RatBall :=
  ⟨⟨-49/320, -113/320⟩, 3/640⟩
def center1346 : GaussianRat :=
  ⟨-120169401/1000000000, -248665661/1000000000⟩
def contact1346 : RatBall := localContactBall tau1346 center1346
def work1346 : RoundedTauEval :=
  evalTau precision tau1346 contact1346 logTwoBall

theorem center_sq1346 : (center1346.re : ℝ)^2 +
    (center1346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1346 : work1346.theta.ok = true ∧
    work1346.jac.invOK = true ∧ acceptsUnitSq work1346.out = true := by decide +kernel

def cell1346 : CellCertificate where
  tauBall := tau1346
  contactCenter := center1346
  contactBall := contact1346
  work := work1346
  center_sq := center_sq1346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1346.1
  jac_ok := checks1346.2.1
  accepted := checks1346.2.2

def tau1347 : RatBall :=
  ⟨⟨-9/64, -23/64⟩, 3/640⟩
def center1347 : GaussianRat :=
  ⟨-889321/8000000, -254626433/1000000000⟩
def contact1347 : RatBall := localContactBall tau1347 center1347
def work1347 : RoundedTauEval :=
  evalTau precision tau1347 contact1347 logTwoBall

theorem center_sq1347 : (center1347.re : ℝ)^2 +
    (center1347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1347 : work1347.theta.ok = true ∧
    work1347.jac.invOK = true ∧ acceptsUnitSq work1347.out = true := by decide +kernel

def cell1347 : CellCertificate where
  tauBall := tau1347
  contactCenter := center1347
  contactBall := contact1347
  work := work1347
  center_sq := center_sq1347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1347.1
  jac_ok := checks1347.2.1
  accepted := checks1347.2.2

def tau1348 : RatBall :=
  ⟨⟨-47/320, -113/320⟩, 3/640⟩
def center1348 : GaussianRat :=
  ⟨-115394221/1000000000, -124626021/500000000⟩
def contact1348 : RatBall := localContactBall tau1348 center1348
def work1348 : RoundedTauEval :=
  evalTau precision tau1348 contact1348 logTwoBall

theorem center_sq1348 : (center1348.re : ℝ)^2 +
    (center1348.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1348]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1348 : work1348.theta.ok = true ∧
    work1348.jac.invOK = true ∧ acceptsUnitSq work1348.out = true := by decide +kernel

def cell1348 : CellCertificate where
  tauBall := tau1348
  contactCenter := center1348
  contactBall := contact1348
  work := work1348
  center_sq := center_sq1348
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1348.1
  jac_ok := checks1348.2.1
  accepted := checks1348.2.2

def tau1349 : RatBall :=
  ⟨⟨-9/64, -113/320⟩, 3/640⟩
def center1349 : GaussianRat :=
  ⟨-22120681/200000000, -249816993/1000000000⟩
def contact1349 : RatBall := localContactBall tau1349 center1349
def work1349 : RoundedTauEval :=
  evalTau precision tau1349 contact1349 logTwoBall

theorem center_sq1349 : (center1349.re : ℝ)^2 +
    (center1349.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1349]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1349 : work1349.theta.ok = true ∧
    work1349.jac.invOK = true ∧ acceptsUnitSq work1349.out = true := by decide +kernel

def cell1349 : CellCertificate where
  tauBall := tau1349
  contactCenter := center1349
  contactBall := contact1349
  work := work1349
  center_sq := center_sq1349
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1349.1
  jac_ok := checks1349.2.1
  accepted := checks1349.2.2

def tau1350 : RatBall :=
  ⟨⟨-43/320, -23/64⟩, 3/640⟩
def center1350 : GaussianRat :=
  ⟨-106336973/1000000000, -255184583/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168


