-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:38:09.413917+00:00
-- url     : https://prove2.me/theorems/d7f52533-0986-4358-9614-ab174263348e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0207.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0207_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1662 : RoundedTauEval :=
  evalTau precision tau1662 contact1662 logTwoBall

theorem center_sq1662 : (center1662.re : ℝ)^2 +
    (center1662.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1662]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1662 : work1662.theta.ok = true ∧
    work1662.jac.invOK = true ∧ acceptsUnitSq work1662.out = true := by decide +kernel

def cell1662 : CellCertificate where
  tauBall := tau1662
  contactCenter := center1662
  contactBall := contact1662
  work := work1662
  center_sq := center_sq1662
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1662.1
  jac_ok := checks1662.2.1
  accepted := checks1662.2.2

def tau1663 : RatBall :=
  ⟨⟨41/320, -111/320⟩, 3/640⟩
def center1663 : GaussianRat :=
  ⟨100474143/1000000000, -123032409/500000000⟩
def contact1663 : RatBall := localContactBall tau1663 center1663
def work1663 : RoundedTauEval :=
  evalTau precision tau1663 contact1663 logTwoBall

theorem center_sq1663 : (center1663.re : ℝ)^2 +
    (center1663.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1663]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1663 : work1663.theta.ok = true ∧
    work1663.jac.invOK = true ∧ acceptsUnitSq work1663.out = true := by decide +kernel

def cell1663 : CellCertificate where
  tauBall := tau1663
  contactCenter := center1663
  contactBall := contact1663
  work := work1663
  center_sq := center_sq1663
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1663.1
  jac_ok := checks1663.2.1
  accepted := checks1663.2.2

def cells : List CellCertificate := [cell1656, cell1657, cell1658, cell1659, cell1660, cell1661, cell1662, cell1663]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207


