-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:44:45.037534+00:00
-- url     : https://prove2.me/theorems/eb3b962e-4991-430d-951a-51a0b141ce3d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0133.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0133_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1070 : (center1070.re : ℝ)^2 +
    (center1070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1070 : work1070.theta.ok = true ∧
    work1070.jac.invOK = true ∧ acceptsUnitSq work1070.out = true := by decide +kernel

def cell1070 : CellCertificate where
  tauBall := tau1070
  contactCenter := center1070
  contactBall := contact1070
  work := work1070
  center_sq := center_sq1070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1070.1
  jac_ok := checks1070.2.1
  accepted := checks1070.2.2

def tau1071 : RatBall :=
  ⟨⟨5/32, 37/160⟩, 3/320⟩
def center1071 : GaussianRat :=
  ⟨113439149/1000000000, 158939613/1000000000⟩
def contact1071 : RatBall := localContactBall tau1071 center1071
def work1071 : RoundedTauEval :=
  evalTau precision tau1071 contact1071 logTwoBall

theorem center_sq1071 : (center1071.re : ℝ)^2 +
    (center1071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1071 : work1071.theta.ok = true ∧
    work1071.jac.invOK = true ∧ acceptsUnitSq work1071.out = true := by decide +kernel

def cell1071 : CellCertificate where
  tauBall := tau1071
  contactCenter := center1071
  contactBall := contact1071
  work := work1071
  center_sq := center_sq1071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1071.1
  jac_ok := checks1071.2.1
  accepted := checks1071.2.2

def cells : List CellCertificate := [cell1064, cell1065, cell1066, cell1067, cell1068, cell1069, cell1070, cell1071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133


