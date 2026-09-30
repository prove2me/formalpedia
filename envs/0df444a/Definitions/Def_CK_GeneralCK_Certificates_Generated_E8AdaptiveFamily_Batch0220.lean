-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0220
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0220
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:00:49.475914+00:00
-- url     : https://prove2.me/theorems/ffe6c546-8f1c-4a95-b1a9-65be0342e4c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0220.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0220_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1766 : (center1766.re : ℝ)^2 +
    (center1766.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1766]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1766 : work1766.theta.ok = true ∧
    work1766.jac.invOK = true ∧ acceptsUnitSq work1766.out = true := by decide +kernel

def cell1766 : CellCertificate where
  tauBall := tau1766
  contactCenter := center1766
  contactBall := contact1766
  work := work1766
  center_sq := center_sq1766
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1766.1
  jac_ok := checks1766.2.1
  accepted := checks1766.2.2

def tau1767 : RatBall :=
  ⟨⟨79/320, -101/320⟩, 3/640⟩
def center1767 : GaussianRat :=
  ⟨92389531/500000000, -210978373/1000000000⟩
def contact1767 : RatBall := localContactBall tau1767 center1767
def work1767 : RoundedTauEval :=
  evalTau precision tau1767 contact1767 logTwoBall

theorem center_sq1767 : (center1767.re : ℝ)^2 +
    (center1767.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1767]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1767 : work1767.theta.ok = true ∧
    work1767.jac.invOK = true ∧ acceptsUnitSq work1767.out = true := by decide +kernel

def cell1767 : CellCertificate where
  tauBall := tau1767
  contactCenter := center1767
  contactBall := contact1767
  work := work1767
  center_sq := center_sq1767
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1767.1
  jac_ok := checks1767.2.1
  accepted := checks1767.2.2

def cells : List CellCertificate := [cell1760, cell1761, cell1762, cell1763, cell1764, cell1765, cell1766, cell1767]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220


