-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0083
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0083
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:56:25.007996+00:00
-- url     : https://prove2.me/theorems/336572d3-be25-4cb9-9923-3a16accdb489
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0083.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0083_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0671 : RatBall :=
  ⟨⟨39/160, -7/32⟩, 3/320⟩
def center0671 : GaussianRat :=
  ⟨173384937/1000000000, -144541281/1000000000⟩
def contact0671 : RatBall := localContactBall tau0671 center0671
def work0671 : RoundedTauEval :=
  evalTau precision tau0671 contact0671 logTwoBall

theorem center_sq0671 : (center0671.re : ℝ)^2 +
    (center0671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0671 : work0671.theta.ok = true ∧
    work0671.jac.invOK = true ∧ acceptsUnitSq work0671.out = true := by decide +kernel

def cell0671 : CellCertificate where
  tauBall := tau0671
  contactCenter := center0671
  contactBall := contact0671
  work := work0671
  center_sq := center_sq0671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0671.1
  jac_ok := checks0671.2.1
  accepted := checks0671.2.2

def cells : List CellCertificate := [cell0664, cell0665, cell0666, cell0667, cell0668, cell0669, cell0670, cell0671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083


