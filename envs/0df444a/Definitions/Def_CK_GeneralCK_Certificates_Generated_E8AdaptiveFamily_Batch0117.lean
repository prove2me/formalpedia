-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:17:05.448492+00:00
-- url     : https://prove2.me/theorems/1f6f9846-32cb-4225-9e2b-b51e9fbe95fd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0117.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0117_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center0943 : GaussianRat :=
  ⟨-21205027/500000000, 199811247/1000000000⟩
def contact0943 : RatBall := localContactBall tau0943 center0943
def work0943 : RoundedTauEval :=
  evalTau precision tau0943 contact0943 logTwoBall

theorem center_sq0943 : (center0943.re : ℝ)^2 +
    (center0943.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0943]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0943 : work0943.theta.ok = true ∧
    work0943.jac.invOK = true ∧ acceptsUnitSq work0943.out = true := by decide +kernel

def cell0943 : CellCertificate where
  tauBall := tau0943
  contactCenter := center0943
  contactBall := contact0943
  work := work0943
  center_sq := center_sq0943
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0943.1
  jac_ok := checks0943.2.1
  accepted := checks0943.2.2

def cells : List CellCertificate := [cell0936, cell0937, cell0938, cell0939, cell0940, cell0941, cell0942, cell0943]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117


