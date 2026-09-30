-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:06:49.242313+00:00
-- url     : https://prove2.me/theorems/693cc99c-4afa-43c2-9404-a262b09c7dfe
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0236.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0236_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1895 : RatBall := localContactBall tau1895 center1895
def work1895 : RoundedTauEval :=
  evalTau precision tau1895 contact1895 logTwoBall

theorem center_sq1895 : (center1895.re : ℝ)^2 +
    (center1895.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1895]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1895 : work1895.theta.ok = true ∧
    work1895.jac.invOK = true ∧ acceptsUnitSq work1895.out = true := by decide +kernel

def cell1895 : CellCertificate where
  tauBall := tau1895
  contactCenter := center1895
  contactBall := contact1895
  work := work1895
  center_sq := center_sq1895
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1895.1
  jac_ok := checks1895.2.1
  accepted := checks1895.2.2

def cells : List CellCertificate := [cell1888, cell1889, cell1890, cell1891, cell1892, cell1893, cell1894, cell1895]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236


