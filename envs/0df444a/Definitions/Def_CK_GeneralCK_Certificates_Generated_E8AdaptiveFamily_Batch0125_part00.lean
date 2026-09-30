-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:09:30.628837+00:00
-- url     : https://prove2.me/theorems/768ea473-3a23-4a80-a02f-de46ce2616a3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0125 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1000 : RatBall :=
  ⟨⟨61/160, 3/32⟩, 3/320⟩
def center1000 : GaussianRat :=
  ⟨50772973/200000000, 14125933/250000000⟩
def contact1000 : RatBall := localContactBall tau1000 center1000
def work1000 : RoundedTauEval :=
  evalTau precision tau1000 contact1000 logTwoBall

theorem center_sq1000 : (center1000.re : ℝ)^2 +
    (center1000.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1000 : work1000.theta.ok = true ∧
    work1000.jac.invOK = true ∧ acceptsUnitSq work1000.out = true := by decide +kernel

def cell1000 : CellCertificate where
  tauBall := tau1000
  contactCenter := center1000
  contactBall := contact1000
  work := work1000
  center_sq := center_sq1000
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1000.1
  jac_ok := checks1000.2.1
  accepted := checks1000.2.2

def tau1001 : RatBall :=
  ⟨⟨63/160, 3/32⟩, 3/320⟩
def center1001 : GaussianRat :=
  ⟨65346019/250000000, 28003013/500000000⟩
def contact1001 : RatBall := localContactBall tau1001 center1001
def work1001 : RoundedTauEval :=
  evalTau precision tau1001 contact1001 logTwoBall

theorem center_sq1001 : (center1001.re : ℝ)^2 +
    (center1001.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1001]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1001 : work1001.theta.ok = true ∧
    work1001.jac.invOK = true ∧ acceptsUnitSq work1001.out = true := by decide +kernel

def cell1001 : CellCertificate where
  tauBall := tau1001
  contactCenter := center1001
  contactBall := contact1001
  work := work1001
  center_sq := center_sq1001
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1001.1
  jac_ok := checks1001.2.1
  accepted := checks1001.2.2

def tau1002 : RatBall :=
  ⟨⟨37/160, 29/160⟩, 3/320⟩
def center1002 : GaussianRat :=
  ⟨81239917/500000000, 60019727/500000000⟩
def contact1002 : RatBall := localContactBall tau1002 center1002
def work1002 : RoundedTauEval :=
  evalTau precision tau1002 contact1002 logTwoBall

theorem center_sq1002 : (center1002.re : ℝ)^2 +
    (center1002.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1002]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1002 : work1002.theta.ok = true ∧
    work1002.jac.invOK = true ∧ acceptsUnitSq work1002.out = true := by decide +kernel

def cell1002 : CellCertificate where
  tauBall := tau1002
  contactCenter := center1002
  contactBall := contact1002
  work := work1002
  center_sq := center_sq1002
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1002.1
  jac_ok := checks1002.2.1
  accepted := checks1002.2.2

def tau1003 : RatBall :=
  ⟨⟨39/160, 29/160⟩, 3/320⟩
def center1003 : GaussianRat :=
  ⟨2135923/12500000, 119305389/1000000000⟩
def contact1003 : RatBall := localContactBall tau1003 center1003
def work1003 : RoundedTauEval :=
  evalTau precision tau1003 contact1003 logTwoBall

theorem center_sq1003 : (center1003.re : ℝ)^2 +
    (center1003.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1003]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125


