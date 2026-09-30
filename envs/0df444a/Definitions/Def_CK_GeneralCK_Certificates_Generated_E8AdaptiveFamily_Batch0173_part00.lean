-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:28:06.083096+00:00
-- url     : https://prove2.me/theorems/b86a9498-9b2c-4396-9659-13785b9d2896
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0173 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1384 : RatBall :=
  ⟨⟨-51/320, -111/320⟩, 3/640⟩
def center1384 : GaussianRat :=
  ⟨-124318847/1000000000, -121658863/500000000⟩
def contact1384 : RatBall := localContactBall tau1384 center1384
def work1384 : RoundedTauEval :=
  evalTau precision tau1384 contact1384 logTwoBall

theorem center_sq1384 : (center1384.re : ℝ)^2 +
    (center1384.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1384]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1384 : work1384.theta.ok = true ∧
    work1384.jac.invOK = true ∧ acceptsUnitSq work1384.out = true := by decide +kernel

def cell1384 : CellCertificate where
  tauBall := tau1384
  contactCenter := center1384
  contactBall := contact1384
  work := work1384
  center_sq := center_sq1384
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1384.1
  jac_ok := checks1384.2.1
  accepted := checks1384.2.2

def tau1385 : RatBall :=
  ⟨⟨-49/320, -111/320⟩, 3/640⟩
def center1385 : GaussianRat :=
  ⟨-29895113/250000000, -121954461/500000000⟩
def contact1385 : RatBall := localContactBall tau1385 center1385
def work1385 : RoundedTauEval :=
  evalTau precision tau1385 contact1385 logTwoBall

theorem center_sq1385 : (center1385.re : ℝ)^2 +
    (center1385.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1385 : work1385.theta.ok = true ∧
    work1385.jac.invOK = true ∧ acceptsUnitSq work1385.out = true := by decide +kernel

def cell1385 : CellCertificate where
  tauBall := tau1385
  contactCenter := center1385
  contactBall := contact1385
  work := work1385
  center_sq := center_sq1385
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1385.1
  jac_ok := checks1385.2.1
  accepted := checks1385.2.2

def tau1386 : RatBall :=
  ⟨⟨-51/320, -109/320⟩, 3/640⟩
def center1386 : GaussianRat :=
  ⟨-61862799/500000000, -238597409/1000000000⟩
def contact1386 : RatBall := localContactBall tau1386 center1386
def work1386 : RoundedTauEval :=
  evalTau precision tau1386 contact1386 logTwoBall

theorem center_sq1386 : (center1386.re : ℝ)^2 +
    (center1386.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1386]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1386 : work1386.theta.ok = true ∧
    work1386.jac.invOK = true ∧ acceptsUnitSq work1386.out = true := by decide +kernel

def cell1386 : CellCertificate where
  tauBall := tau1386
  contactCenter := center1386
  contactBall := contact1386
  work := work1386
  center_sq := center_sq1386
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1386.1
  jac_ok := checks1386.2.1
  accepted := checks1386.2.2

def tau1387 : RatBall :=
  ⟨⟨-49/320, -109/320⟩, 3/640⟩
def center1387 : GaussianRat :=
  ⟨-119007309/1000000000, -59793181/250000000⟩
def contact1387 : RatBall := localContactBall tau1387 center1387
def work1387 : RoundedTauEval :=
  evalTau precision tau1387 contact1387 logTwoBall

theorem center_sq1387 : (center1387.re : ℝ)^2 +
    (center1387.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1387]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1387 : work1387.theta.ok = true ∧
    work1387.jac.invOK = true ∧ acceptsUnitSq work1387.out = true := by decide +kernel

def cell1387 : CellCertificate where
  tauBall := tau1387
  contactCenter := center1387
  contactBall := contact1387
  work := work1387
  center_sq := center_sq1387
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1387.1
  jac_ok := checks1387.2.1
  accepted := checks1387.2.2

def tau1388 : RatBall :=
  ⟨⟨-11/64, -107/320⟩, 3/640⟩
def center1388 : GaussianRat :=
  ⟨-66249189/500000000, -232719989/1000000000⟩
def contact1388 : RatBall := localContactBall tau1388 center1388
def work1388 : RoundedTauEval :=
  evalTau precision tau1388 contact1388 logTwoBall

theorem center_sq1388 : (center1388.re : ℝ)^2 +
    (center1388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1388 : work1388.theta.ok = true ∧
    work1388.jac.invOK = true ∧ acceptsUnitSq work1388.out = true := by decide +kernel

def cell1388 : CellCertificate where
  tauBall := tau1388
  contactCenter := center1388
  contactBall := contact1388
  work := work1388
  center_sq := center_sq1388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1388.1
  jac_ok := checks1388.2.1
  accepted := checks1388.2.2

def tau1389 : RatBall :=
  ⟨⟨-53/320, -107/320⟩, 3/640⟩
def center1389 : GaussianRat :=
  ⟨-15978923/125000000, -233317801/1000000000⟩
def contact1389 : RatBall := localContactBall tau1389 center1389
def work1389 : RoundedTauEval :=
  evalTau precision tau1389 contact1389 logTwoBall

theorem center_sq1389 : (center1389.re : ℝ)^2 +
    (center1389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1389 : work1389.theta.ok = true ∧
    work1389.jac.invOK = true ∧ acceptsUnitSq work1389.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173


