-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:19:53.47292+00:00
-- url     : https://prove2.me/theorems/6bc168f4-5e42-43e4-bfed-77af93fb5da0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0210.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0210_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1686 : (center1686.re : ℝ)^2 +
    (center1686.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1686]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1686 : work1686.theta.ok = true ∧
    work1686.jac.invOK = true ∧ acceptsUnitSq work1686.out = true := by decide +kernel

def cell1686 : CellCertificate where
  tauBall := tau1686
  contactCenter := center1686
  contactBall := contact1686
  work := work1686
  center_sq := center_sq1686
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1686.1
  jac_ok := checks1686.2.1
  accepted := checks1686.2.2

def tau1687 : RatBall :=
  ⟨⟨53/320, -111/320⟩, 3/640⟩
def center1687 : GaussianRat :=
  ⟨4032529/31250000, -121353177/500000000⟩
def contact1687 : RatBall := localContactBall tau1687 center1687
def work1687 : RoundedTauEval :=
  evalTau precision tau1687 contact1687 logTwoBall

theorem center_sq1687 : (center1687.re : ℝ)^2 +
    (center1687.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1687]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1687 : work1687.theta.ok = true ∧
    work1687.jac.invOK = true ∧ acceptsUnitSq work1687.out = true := by decide +kernel

def cell1687 : CellCertificate where
  tauBall := tau1687
  contactCenter := center1687
  contactBall := contact1687
  work := work1687
  center_sq := center_sq1687
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1687.1
  jac_ok := checks1687.2.1
  accepted := checks1687.2.2

def cells : List CellCertificate := [cell1680, cell1681, cell1682, cell1683, cell1684, cell1685, cell1686, cell1687]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210


