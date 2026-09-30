-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:41:05.870462+00:00
-- url     : https://prove2.me/theorems/431866d1-1e04-4c99-b5f9-a543173b71a0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0134.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0134_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1076 : GaussianRat :=
  ⟨139868391/1000000000, 78332251/500000000⟩
def contact1076 : RatBall := localContactBall tau1076 center1076
def work1076 : RoundedTauEval :=
  evalTau precision tau1076 contact1076 logTwoBall

theorem center_sq1076 : (center1076.re : ℝ)^2 +
    (center1076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1076 : work1076.theta.ok = true ∧
    work1076.jac.invOK = true ∧ acceptsUnitSq work1076.out = true := by decide +kernel

def cell1076 : CellCertificate where
  tauBall := tau1076
  contactCenter := center1076
  contactBall := contact1076
  work := work1076
  center_sq := center_sq1076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1076.1
  jac_ok := checks1076.2.1
  accepted := checks1076.2.2

def tau1077 : RatBall :=
  ⟨⟨29/160, 39/160⟩, 3/320⟩
def center1077 : GaussianRat :=
  ⟨131916433/1000000000, 83139101/500000000⟩
def contact1077 : RatBall := localContactBall tau1077 center1077
def work1077 : RoundedTauEval :=
  evalTau precision tau1077 contact1077 logTwoBall

theorem center_sq1077 : (center1077.re : ℝ)^2 +
    (center1077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1077 : work1077.theta.ok = true ∧
    work1077.jac.invOK = true ∧ acceptsUnitSq work1077.out = true := by decide +kernel

def cell1077 : CellCertificate where
  tauBall := tau1077
  contactCenter := center1077
  contactBall := contact1077
  work := work1077
  center_sq := center_sq1077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1077.1
  jac_ok := checks1077.2.1
  accepted := checks1077.2.2

def tau1078 : RatBall :=
  ⟨⟨31/160, 39/160⟩, 3/320⟩
def center1078 : GaussianRat :=
  ⟨2814451/20000000, 33084071/200000000⟩
def contact1078 : RatBall := localContactBall tau1078 center1078
def work1078 : RoundedTauEval :=
  evalTau precision tau1078 contact1078 logTwoBall

theorem center_sq1078 : (center1078.re : ℝ)^2 +
    (center1078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1078 : work1078.theta.ok = true ∧
    work1078.jac.invOK = true ∧ acceptsUnitSq work1078.out = true := by decide +kernel

def cell1078 : CellCertificate where
  tauBall := tau1078
  contactCenter := center1078
  contactBall := contact1078
  work := work1078
  center_sq := center_sq1078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1078.1
  jac_ok := checks1078.2.1
  accepted := checks1078.2.2

def tau1079 : RatBall :=
  ⟨⟨17/160, 41/160⟩, 3/320⟩
def center1079 : GaussianRat :=
  ⟨1572299/20000000, 179469913/1000000000⟩
def contact1079 : RatBall := localContactBall tau1079 center1079
def work1079 : RoundedTauEval :=
  evalTau precision tau1079 contact1079 logTwoBall

theorem center_sq1079 : (center1079.re : ℝ)^2 +
    (center1079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1079 : work1079.theta.ok = true ∧
    work1079.jac.invOK = true ∧ acceptsUnitSq work1079.out = true := by decide +kernel

def cell1079 : CellCertificate where
  tauBall := tau1079
  contactCenter := center1079
  contactBall := contact1079
  work := work1079
  center_sq := center_sq1079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1079.1
  jac_ok := checks1079.2.1
  accepted := checks1079.2.2

def cells : List CellCertificate := [cell1072, cell1073, cell1074, cell1075, cell1076, cell1077, cell1078, cell1079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134


