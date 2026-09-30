-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:55:59.921041+00:00
-- url     : https://prove2.me/theorems/c37da8f2-edda-4f76-a1a0-36406021f036
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0127.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1023 : GaussianRat :=
  ⟨216902699/1000000000, 20636751/250000000⟩
def contact1023 : RatBall := localContactBall tau1023 center1023
def work1023 : RoundedTauEval :=
  evalTau precision tau1023 contact1023 logTwoBall

theorem center_sq1023 : (center1023.re : ℝ)^2 +
    (center1023.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1023 : work1023.theta.ok = true ∧
    work1023.jac.invOK = true ∧ acceptsUnitSq work1023.out = true := by decide +kernel

def cell1023 : CellCertificate where
  tauBall := tau1023
  contactCenter := center1023
  contactBall := contact1023
  work := work1023
  center_sq := center_sq1023
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1023.1
  jac_ok := checks1023.2.1
  accepted := checks1023.2.2

def cells : List CellCertificate := [cell1016, cell1017, cell1018, cell1019, cell1020, cell1021, cell1022, cell1023]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127


