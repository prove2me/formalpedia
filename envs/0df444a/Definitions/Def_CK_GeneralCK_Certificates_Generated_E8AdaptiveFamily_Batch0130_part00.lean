-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:09:05.742185+00:00
-- url     : https://prove2.me/theorems/327b9b67-c030-4e5a-9d35-8c60be889b12
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0130 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1040 : RatBall :=
  ⟨⟨61/160, 21/160⟩, 3/320⟩
def center1040 : GaussianRat :=
  ⟨15978319/62500000, 79201909/1000000000⟩
def contact1040 : RatBall := localContactBall tau1040 center1040
def work1040 : RoundedTauEval :=
  evalTau precision tau1040 contact1040 logTwoBall

theorem center_sq1040 : (center1040.re : ℝ)^2 +
    (center1040.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1040]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1040 : work1040.theta.ok = true ∧
    work1040.jac.invOK = true ∧ acceptsUnitSq work1040.out = true := by decide +kernel

def cell1040 : CellCertificate where
  tauBall := tau1040
  contactCenter := center1040
  contactBall := contact1040
  work := work1040
  center_sq := center_sq1040
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1040.1
  jac_ok := checks1040.2.1
  accepted := checks1040.2.2

def tau1041 : RatBall :=
  ⟨⟨61/160, 23/160⟩, 3/320⟩
def center1041 : GaussianRat :=
  ⟨64096843/250000000, 86787913/1000000000⟩
def contact1041 : RatBall := localContactBall tau1041 center1041
def work1041 : RoundedTauEval :=
  evalTau precision tau1041 contact1041 logTwoBall

theorem center_sq1041 : (center1041.re : ℝ)^2 +
    (center1041.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1041]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1041 : work1041.theta.ok = true ∧
    work1041.jac.invOK = true ∧ acceptsUnitSq work1041.out = true := by decide +kernel

def cell1041 : CellCertificate where
  tauBall := tau1041
  contactCenter := center1041
  contactBall := contact1041
  work := work1041
  center_sq := center_sq1041
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1041.1
  jac_ok := checks1041.2.1
  accepted := checks1041.2.2

def tau1042 : RatBall :=
  ⟨⟨49/160, 5/32⟩, 3/320⟩
def center1042 : GaussianRat :=
  ⟨52580197/250000000, 1239543/12500000⟩
def contact1042 : RatBall := localContactBall tau1042 center1042
def work1042 : RoundedTauEval :=
  evalTau precision tau1042 contact1042 logTwoBall

theorem center_sq1042 : (center1042.re : ℝ)^2 +
    (center1042.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1042]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1042 : work1042.theta.ok = true ∧
    work1042.jac.invOK = true ∧ acceptsUnitSq work1042.out = true := by decide +kernel

def cell1042 : CellCertificate where
  tauBall := tau1042
  contactCenter := center1042
  contactBall := contact1042
  work := work1042
  center_sq := center_sq1042
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1042.1
  jac_ok := checks1042.2.1
  accepted := checks1042.2.2

def tau1043 : RatBall :=
  ⟨⟨51/160, 5/32⟩, 3/320⟩
def center1043 : GaussianRat :=
  ⟨5457529/25000000, 49204231/500000000⟩
def contact1043 : RatBall := localContactBall tau1043 center1043
def work1043 : RoundedTauEval :=
  evalTau precision tau1043 contact1043 logTwoBall

theorem center_sq1043 : (center1043.re : ℝ)^2 +
    (center1043.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1043]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1043 : work1043.theta.ok = true ∧
    work1043.jac.invOK = true ∧ acceptsUnitSq work1043.out = true := by decide +kernel

def cell1043 : CellCertificate where
  tauBall := tau1043
  contactCenter := center1043
  contactBall := contact1043
  work := work1043
  center_sq := center_sq1043
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1043.1
  jac_ok := checks1043.2.1
  accepted := checks1043.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130


