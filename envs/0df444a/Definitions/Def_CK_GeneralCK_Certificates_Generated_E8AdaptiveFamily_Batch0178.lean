-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:35:19.433514+00:00
-- url     : https://prove2.me/theorems/492f53be-13e6-4314-9b1d-7e12f9210d74
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0178.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0178_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1430 : work1430.theta.ok = true ∧
    work1430.jac.invOK = true ∧ acceptsUnitSq work1430.out = true := by decide +kernel

def cell1430 : CellCertificate where
  tauBall := tau1430
  contactCenter := center1430
  contactBall := contact1430
  work := work1430
  center_sq := center_sq1430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1430.1
  jac_ok := checks1430.2.1
  accepted := checks1430.2.2

def tau1431 : RatBall :=
  ⟨⟨-9/64, -21/64⟩, 3/640⟩
def center1431 : GaussianRat :=
  ⟨-21700807/200000000, -115395841/500000000⟩
def contact1431 : RatBall := localContactBall tau1431 center1431
def work1431 : RoundedTauEval :=
  evalTau precision tau1431 contact1431 logTwoBall

theorem center_sq1431 : (center1431.re : ℝ)^2 +
    (center1431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1431 : work1431.theta.ok = true ∧
    work1431.jac.invOK = true ∧ acceptsUnitSq work1431.out = true := by decide +kernel

def cell1431 : CellCertificate where
  tauBall := tau1431
  contactCenter := center1431
  contactBall := contact1431
  work := work1431
  center_sq := center_sq1431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1431.1
  jac_ok := checks1431.2.1
  accepted := checks1431.2.2

def cells : List CellCertificate := [cell1424, cell1425, cell1426, cell1427, cell1428, cell1429, cell1430, cell1431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178


