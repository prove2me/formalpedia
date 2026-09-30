-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:14:54.129564+00:00
-- url     : https://prove2.me/theorems/0734e387-0554-49ed-8def-65be882c9a32
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0171 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1368 : RatBall :=
  ⟨⟨-59/320, -111/320⟩, 3/640⟩
def center1368 : GaussianRat :=
  ⟨-143104409/1000000000, -240754941/1000000000⟩
def contact1368 : RatBall := localContactBall tau1368 center1368
def work1368 : RoundedTauEval :=
  evalTau precision tau1368 contact1368 logTwoBall

theorem center_sq1368 : (center1368.re : ℝ)^2 +
    (center1368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1368 : work1368.theta.ok = true ∧
    work1368.jac.invOK = true ∧ acceptsUnitSq work1368.out = true := by decide +kernel

def cell1368 : CellCertificate where
  tauBall := tau1368
  contactCenter := center1368
  contactBall := contact1368
  work := work1368
  center_sq := center_sq1368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1368.1
  jac_ok := checks1368.2.1
  accepted := checks1368.2.2

def tau1369 : RatBall :=
  ⟨⟨-57/320, -111/320⟩, 3/640⟩
def center1369 : GaussianRat :=
  ⟨-138434183/1000000000, -120712289/500000000⟩
def contact1369 : RatBall := localContactBall tau1369 center1369
def work1369 : RoundedTauEval :=
  evalTau precision tau1369 contact1369 logTwoBall

theorem center_sq1369 : (center1369.re : ℝ)^2 +
    (center1369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1369 : work1369.theta.ok = true ∧
    work1369.jac.invOK = true ∧ acceptsUnitSq work1369.out = true := by decide +kernel

def cell1369 : CellCertificate where
  tauBall := tau1369
  contactCenter := center1369
  contactBall := contact1369
  work := work1369
  center_sq := center_sq1369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1369.1
  jac_ok := checks1369.2.1
  accepted := checks1369.2.2

def tau1370 : RatBall :=
  ⟨⟨-59/320, -109/320⟩, 3/640⟩
def center1370 : GaussianRat :=
  ⟨-71217211/500000000, -236102993/1000000000⟩
def contact1370 : RatBall := localContactBall tau1370 center1370
def work1370 : RoundedTauEval :=
  evalTau precision tau1370 contact1370 logTwoBall

theorem center_sq1370 : (center1370.re : ℝ)^2 +
    (center1370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1370 : work1370.theta.ok = true ∧
    work1370.jac.invOK = true ∧ acceptsUnitSq work1370.out = true := by decide +kernel

def cell1370 : CellCertificate where
  tauBall := tau1370
  contactCenter := center1370
  contactBall := contact1370
  work := work1370
  center_sq := center_sq1370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1370.1
  jac_ok := checks1370.2.1
  accepted := checks1370.2.2

def tau1371 : RatBall :=
  ⟨⟨-57/320, -109/320⟩, 3/640⟩
def center1371 : GaussianRat :=
  ⟨-137782813/1000000000, -5918871/25000000⟩
def contact1371 : RatBall := localContactBall tau1371 center1371
def work1371 : RoundedTauEval :=
  evalTau precision tau1371 contact1371 logTwoBall

theorem center_sq1371 : (center1371.re : ℝ)^2 +
    (center1371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1371 : work1371.theta.ok = true ∧
    work1371.jac.invOK = true ∧ acceptsUnitSq work1371.out = true := by decide +kernel

def cell1371 : CellCertificate where
  tauBall := tau1371
  contactCenter := center1371
  contactBall := contact1371
  work := work1371
  center_sq := center_sq1371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1371.1
  jac_ok := checks1371.2.1
  accepted := checks1371.2.2

def tau1372 : RatBall :=
  ⟨⟨-63/320, -107/320⟩, 3/640⟩
def center1372 : GaussianRat :=
  ⟨-150996377/1000000000, -230147447/1000000000⟩
def contact1372 : RatBall := localContactBall tau1372 center1372
def work1372 : RoundedTauEval :=
  evalTau precision tau1372 contact1372 logTwoBall

theorem center_sq1372 : (center1372.re : ℝ)^2 +
    (center1372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1372 : work1372.theta.ok = true ∧
    work1372.jac.invOK = true ∧ acceptsUnitSq work1372.out = true := by decide +kernel

def cell1372 : CellCertificate where
  tauBall := tau1372
  contactCenter := center1372
  contactBall := contact1372
  work := work1372
  center_sq := center_sq1372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1372.1
  jac_ok := checks1372.2.1
  accepted := checks1372.2.2

def tau1373 : RatBall :=
  ⟨⟨-61/320, -107/320⟩, 3/640⟩
def center1373 : GaussianRat :=
  ⟨-146398251/1000000000, -115408523/500000000⟩
def contact1373 : RatBall := localContactBall tau1373 center1373
def work1373 : RoundedTauEval :=
  evalTau precision tau1373 contact1373 logTwoBall

theorem center_sq1373 : (center1373.re : ℝ)^2 +
    (center1373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1373 : work1373.theta.ok = true ∧
    work1373.jac.invOK = true ∧ acceptsUnitSq work1373.out = true := by decide +kernel

def cell1373 : CellCertificate where
  tauBall := tau1373
  contactCenter := center1373
  contactBall := contact1373
  work := work1373
  center_sq := center_sq1373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1373.1
  jac_ok := checks1373.2.1
  accepted := checks1373.2.2

def tau1374 : RatBall :=
  ⟨⟨-63/320, -21/64⟩, 3/640⟩
def center1374 : GaussianRat :=
  ⟨-75163641/500000000, -225566837/1000000000⟩
def contact1374 : RatBall := localContactBall tau1374 center1374
def work1374 : RoundedTauEval :=
  evalTau precision tau1374 contact1374 logTwoBall

theorem center_sq1374 : (center1374.re : ℝ)^2 +
    (center1374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1374]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171


