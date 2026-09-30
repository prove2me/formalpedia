-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:22:04.967346+00:00
-- url     : https://prove2.me/theorems/ac3536a3-5c12-43e5-b78f-5d559967c470
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0081.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0654 : (center0654.re : ℝ)^2 +
    (center0654.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0654]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0654 : work0654.theta.ok = true ∧
    work0654.jac.invOK = true ∧ acceptsUnitSq work0654.out = true := by decide +kernel

def cell0654 : CellCertificate where
  tauBall := tau0654
  contactCenter := center0654
  contactBall := contact0654
  work := work0654
  center_sq := center_sq0654
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0654.1
  jac_ok := checks0654.2.1
  accepted := checks0654.2.2

def tau0655 : RatBall :=
  ⟨⟨39/160, -41/160⟩, 3/320⟩
def center0655 : GaussianRat :=
  ⟨44113519/250000000, -170094077/1000000000⟩
def contact0655 : RatBall := localContactBall tau0655 center0655
def work0655 : RoundedTauEval :=
  evalTau precision tau0655 contact0655 logTwoBall

theorem center_sq0655 : (center0655.re : ℝ)^2 +
    (center0655.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0655]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0655 : work0655.theta.ok = true ∧
    work0655.jac.invOK = true ∧ acceptsUnitSq work0655.out = true := by decide +kernel

def cell0655 : CellCertificate where
  tauBall := tau0655
  contactCenter := center0655
  contactBall := contact0655
  work := work0655
  center_sq := center_sq0655
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0655.1
  jac_ok := checks0655.2.1
  accepted := checks0655.2.2

def cells : List CellCertificate := [cell0648, cell0649, cell0650, cell0651, cell0652, cell0653, cell0654, cell0655]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081


