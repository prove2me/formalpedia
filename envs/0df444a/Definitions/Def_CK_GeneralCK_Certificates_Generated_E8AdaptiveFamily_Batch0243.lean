-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:53:59.819048+00:00
-- url     : https://prove2.me/theorems/a7d4aac8-7e5b-4993-8a5f-585f8a6e2d88
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0243.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1951 : RatBall := localContactBall tau1951 center1951
def work1951 : RoundedTauEval :=
  evalTau precision tau1951 contact1951 logTwoBall

theorem center_sq1951 : (center1951.re : ℝ)^2 +
    (center1951.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1951]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1951 : work1951.theta.ok = true ∧
    work1951.jac.invOK = true ∧ acceptsUnitSq work1951.out = true := by decide +kernel

def cell1951 : CellCertificate where
  tauBall := tau1951
  contactCenter := center1951
  contactBall := contact1951
  work := work1951
  center_sq := center_sq1951
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1951.1
  jac_ok := checks1951.2.1
  accepted := checks1951.2.2

def cells : List CellCertificate := [cell1944, cell1945, cell1946, cell1947, cell1948, cell1949, cell1950, cell1951]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243


