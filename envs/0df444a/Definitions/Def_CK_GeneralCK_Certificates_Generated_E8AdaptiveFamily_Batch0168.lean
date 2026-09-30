-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:26:07.250179+00:00
-- url     : https://prove2.me/theorems/d664f299-b8d3-404b-84dc-b06cd019fe0e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0168.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0168_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1350 : RatBall := localContactBall tau1350 center1350
def work1350 : RoundedTauEval :=
  evalTau precision tau1350 contact1350 logTwoBall

theorem center_sq1350 : (center1350.re : ℝ)^2 +
    (center1350.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1350]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1350 : work1350.theta.ok = true ∧
    work1350.jac.invOK = true ∧ acceptsUnitSq work1350.out = true := by decide +kernel

def cell1350 : CellCertificate where
  tauBall := tau1350
  contactCenter := center1350
  contactBall := contact1350
  work := work1350
  center_sq := center_sq1350
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1350.1
  jac_ok := checks1350.2.1
  accepted := checks1350.2.2

def tau1351 : RatBall :=
  ⟨⟨-41/320, -23/64⟩, 3/640⟩
def center1351 : GaussianRat :=
  ⟨-12686743/125000000, -255720023/1000000000⟩
def contact1351 : RatBall := localContactBall tau1351 center1351
def work1351 : RoundedTauEval :=
  evalTau precision tau1351 contact1351 logTwoBall

theorem center_sq1351 : (center1351.re : ℝ)^2 +
    (center1351.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1351]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1351 : work1351.theta.ok = true ∧
    work1351.jac.invOK = true ∧ acceptsUnitSq work1351.out = true := by decide +kernel

def cell1351 : CellCertificate where
  tauBall := tau1351
  contactCenter := center1351
  contactBall := contact1351
  work := work1351
  center_sq := center_sq1351
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1351.1
  jac_ok := checks1351.2.1
  accepted := checks1351.2.2

def cells : List CellCertificate := [cell1344, cell1345, cell1346, cell1347, cell1348, cell1349, cell1350, cell1351]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168


