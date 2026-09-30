-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:01.599048+00:00
-- url     : https://prove2.me/theorems/025b4b96-2b8e-4c47-a909-c10f2cccfb12
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0135 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0135_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1084 : RatBall :=
  ⟨⟨23/160, 41/160⟩, 3/320⟩
def center1084 : GaussianRat :=
  ⟨105897059/1000000000, 22194707/125000000⟩
def contact1084 : RatBall := localContactBall tau1084 center1084
def work1084 : RoundedTauEval :=
  evalTau precision tau1084 contact1084 logTwoBall

theorem center_sq1084 : (center1084.re : ℝ)^2 +
    (center1084.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1084]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1084 : work1084.theta.ok = true ∧
    work1084.jac.invOK = true ∧ acceptsUnitSq work1084.out = true := by decide +kernel

def cell1084 : CellCertificate where
  tauBall := tau1084
  contactCenter := center1084
  contactBall := contact1084
  work := work1084
  center_sq := center_sq1084
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1084.1
  jac_ok := checks1084.2.1
  accepted := checks1084.2.2

def tau1085 : RatBall :=
  ⟨⟨21/160, 43/160⟩, 3/320⟩
def center1085 : GaussianRat :=
  ⟨1523927/15625000, 46839637/250000000⟩
def contact1085 : RatBall := localContactBall tau1085 center1085
def work1085 : RoundedTauEval :=
  evalTau precision tau1085 contact1085 logTwoBall

theorem center_sq1085 : (center1085.re : ℝ)^2 +
    (center1085.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1085]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1085 : work1085.theta.ok = true ∧
    work1085.jac.invOK = true ∧ acceptsUnitSq work1085.out = true := by decide +kernel

def cell1085 : CellCertificate where
  tauBall := tau1085
  contactCenter := center1085
  contactBall := contact1085
  work := work1085
  center_sq := center_sq1085
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1085.1
  jac_ok := checks1085.2.1
  accepted := checks1085.2.2

def tau1086 : RatBall :=
  ⟨⟨23/160, 43/160⟩, 3/320⟩
def center1086 : GaussianRat :=
  ⟨106644393/1000000000, 93309307/500000000⟩
def contact1086 : RatBall := localContactBall tau1086 center1086
def work1086 : RoundedTauEval :=
  evalTau precision tau1086 contact1086 logTwoBall

theorem center_sq1086 : (center1086.re : ℝ)^2 +
    (center1086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1086 : work1086.theta.ok = true ∧
    work1086.jac.invOK = true ∧ acceptsUnitSq work1086.out = true := by decide +kernel

def cell1086 : CellCertificate where
  tauBall := tau1086
  contactCenter := center1086
  contactBall := contact1086
  work := work1086
  center_sq := center_sq1086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1086.1
  jac_ok := checks1086.2.1
  accepted := checks1086.2.2

def tau1087 : RatBall :=
  ⟨⟨17/160, 9/32⟩, 3/320⟩
def center1087 : GaussianRat :=
  ⟨19945259/250000000, 39579621/200000000⟩
def contact1087 : RatBall := localContactBall tau1087 center1087
def work1087 : RoundedTauEval :=
  evalTau precision tau1087 contact1087 logTwoBall

theorem center_sq1087 : (center1087.re : ℝ)^2 +
    (center1087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1087 : work1087.theta.ok = true ∧
    work1087.jac.invOK = true ∧ acceptsUnitSq work1087.out = true := by decide +kernel

def cell1087 : CellCertificate where
  tauBall := tau1087
  contactCenter := center1087
  contactBall := contact1087
  work := work1087
  center_sq := center_sq1087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1087.1
  jac_ok := checks1087.2.1
  accepted := checks1087.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135


