-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:00.880989+00:00
-- url     : https://prove2.me/theorems/db6f5c93-e632-44c1-8a0d-a89679df726c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0214.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0214_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1718 : GaussianRat :=
  ⟨8207299/62500000, -8937551/40000000⟩
def contact1718 : RatBall := localContactBall tau1718 center1718
def work1718 : RoundedTauEval :=
  evalTau precision tau1718 contact1718 logTwoBall

theorem center_sq1718 : (center1718.re : ℝ)^2 +
    (center1718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1718 : work1718.theta.ok = true ∧
    work1718.jac.invOK = true ∧ acceptsUnitSq work1718.out = true := by decide +kernel

def cell1718 : CellCertificate where
  tauBall := tau1718
  contactCenter := center1718
  contactBall := contact1718
  work := work1718
  center_sq := center_sq1718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1718.1
  jac_ok := checks1718.2.1
  accepted := checks1718.2.2

def tau1719 : RatBall :=
  ⟨⟨53/320, -101/320⟩, 3/640⟩
def center1719 : GaussianRat :=
  ⟨15767113/125000000, -219375147/1000000000⟩
def contact1719 : RatBall := localContactBall tau1719 center1719
def work1719 : RoundedTauEval :=
  evalTau precision tau1719 contact1719 logTwoBall

theorem center_sq1719 : (center1719.re : ℝ)^2 +
    (center1719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1719 : work1719.theta.ok = true ∧
    work1719.jac.invOK = true ∧ acceptsUnitSq work1719.out = true := by decide +kernel

def cell1719 : CellCertificate where
  tauBall := tau1719
  contactCenter := center1719
  contactBall := contact1719
  work := work1719
  center_sq := center_sq1719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1719.1
  jac_ok := checks1719.2.1
  accepted := checks1719.2.2

def cells : List CellCertificate := [cell1712, cell1713, cell1714, cell1715, cell1716, cell1717, cell1718, cell1719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214


