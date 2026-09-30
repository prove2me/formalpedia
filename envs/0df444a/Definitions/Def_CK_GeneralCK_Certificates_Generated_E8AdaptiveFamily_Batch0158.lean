-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:02:10.860067+00:00
-- url     : https://prove2.me/theorems/85497233-08d6-41c7-99ff-dd2693dbde41
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0158.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0158_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1269 : (center1269.re : ℝ)^2 +
    (center1269.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1269]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1269 : work1269.theta.ok = true ∧
    work1269.jac.invOK = true ∧ acceptsUnitSq work1269.out = true := by decide +kernel

def cell1269 : CellCertificate where
  tauBall := tau1269
  contactCenter := center1269
  contactBall := contact1269
  work := work1269
  center_sq := center_sq1269
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1269.1
  jac_ok := checks1269.2.1
  accepted := checks1269.2.2

def tau1270 : RatBall :=
  ⟨⟨-89/320, -93/320⟩, 3/640⟩
def center1270 : GaussianRat :=
  ⟨-50860061/250000000, -2969643/15625000⟩
def contact1270 : RatBall := localContactBall tau1270 center1270
def work1270 : RoundedTauEval :=
  evalTau precision tau1270 contact1270 logTwoBall

theorem center_sq1270 : (center1270.re : ℝ)^2 +
    (center1270.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1270]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1270 : work1270.theta.ok = true ∧
    work1270.jac.invOK = true ∧ acceptsUnitSq work1270.out = true := by decide +kernel

def cell1270 : CellCertificate where
  tauBall := tau1270
  contactCenter := center1270
  contactBall := contact1270
  work := work1270
  center_sq := center_sq1270
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1270.1
  jac_ok := checks1270.2.1
  accepted := checks1270.2.2

def tau1271 : RatBall :=
  ⟨⟨-93/320, -89/320⟩, 3/640⟩
def center1271 : GaussianRat :=
  ⟨-84181/400000, -180208911/1000000000⟩
def contact1271 : RatBall := localContactBall tau1271 center1271
def work1271 : RoundedTauEval :=
  evalTau precision tau1271 contact1271 logTwoBall

theorem center_sq1271 : (center1271.re : ℝ)^2 +
    (center1271.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1271]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1271 : work1271.theta.ok = true ∧
    work1271.jac.invOK = true ∧ acceptsUnitSq work1271.out = true := by decide +kernel

def cell1271 : CellCertificate where
  tauBall := tau1271
  contactCenter := center1271
  contactBall := contact1271
  work := work1271
  center_sq := center_sq1271
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1271.1
  jac_ok := checks1271.2.1
  accepted := checks1271.2.2

def cells : List CellCertificate := [cell1264, cell1265, cell1266, cell1267, cell1268, cell1269, cell1270, cell1271]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158


