-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0139_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:09:18.702143+00:00
-- url     : https://prove2.me/theorems/9c0ae24e-0496-4654-a462-5d6e38d3ee14
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0139 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1112 : RatBall :=
  ⟨⟨3/160, 49/160⟩, 3/320⟩
def center1112 : GaussianRat :=
  ⟨14395497/1000000000, 27438463/125000000⟩
def contact1112 : RatBall := localContactBall tau1112 center1112
def work1112 : RoundedTauEval :=
  evalTau precision tau1112 contact1112 logTwoBall

theorem center_sq1112 : (center1112.re : ℝ)^2 +
    (center1112.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1112]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1112 : work1112.theta.ok = true ∧
    work1112.jac.invOK = true ∧ acceptsUnitSq work1112.out = true := by decide +kernel

def cell1112 : CellCertificate where
  tauBall := tau1112
  contactCenter := center1112
  contactBall := contact1112
  work := work1112
  center_sq := center_sq1112
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1112.1
  jac_ok := checks1112.2.1
  accepted := checks1112.2.2

def tau1113 : RatBall :=
  ⟨⟨1/160, 51/160⟩, 3/320⟩
def center1113 : GaussianRat :=
  ⟨4842747/1000000000, 45846653/200000000⟩
def contact1113 : RatBall := localContactBall tau1113 center1113
def work1113 : RoundedTauEval :=
  evalTau precision tau1113 contact1113 logTwoBall

theorem center_sq1113 : (center1113.re : ℝ)^2 +
    (center1113.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1113]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1113 : work1113.theta.ok = true ∧
    work1113.jac.invOK = true ∧ acceptsUnitSq work1113.out = true := by decide +kernel

def cell1113 : CellCertificate where
  tauBall := tau1113
  contactCenter := center1113
  contactBall := contact1113
  work := work1113
  center_sq := center_sq1113
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1113.1
  jac_ok := checks1113.2.1
  accepted := checks1113.2.2

def tau1114 : RatBall :=
  ⟨⟨3/160, 51/160⟩, 3/320⟩
def center1114 : GaussianRat :=
  ⟨581027/40000000, 57285979/250000000⟩
def contact1114 : RatBall := localContactBall tau1114 center1114
def work1114 : RoundedTauEval :=
  evalTau precision tau1114 contact1114 logTwoBall

theorem center_sq1114 : (center1114.re : ℝ)^2 +
    (center1114.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1114]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1114 : work1114.theta.ok = true ∧
    work1114.jac.invOK = true ∧ acceptsUnitSq work1114.out = true := by decide +kernel

def cell1114 : CellCertificate where
  tauBall := tau1114
  contactCenter := center1114
  contactBall := contact1114
  work := work1114
  center_sq := center_sq1114
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1114.1
  jac_ok := checks1114.2.1
  accepted := checks1114.2.2

def tau1115 : RatBall :=
  ⟨⟨1/32, 49/160⟩, 3/320⟩
def center1115 : GaussianRat :=
  ⟨2398433/100000000, 219339251/1000000000⟩
def contact1115 : RatBall := localContactBall tau1115 center1115
def work1115 : RoundedTauEval :=
  evalTau precision tau1115 contact1115 logTwoBall

theorem center_sq1115 : (center1115.re : ℝ)^2 +
    (center1115.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1115]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139


