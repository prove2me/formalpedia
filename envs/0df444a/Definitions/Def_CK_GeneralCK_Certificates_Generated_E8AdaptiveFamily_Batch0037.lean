-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:05:26.876037+00:00
-- url     : https://prove2.me/theorems/f2d9f3b0-2015-42b0-a594-190820f652ca
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0037.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0037_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0302 : (center0302.re : ℝ)^2 +
    (center0302.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0302]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0302 : work0302.theta.ok = true ∧
    work0302.jac.invOK = true ∧ acceptsUnitSq work0302.out = true := by decide +kernel

def cell0302 : CellCertificate where
  tauBall := tau0302
  contactCenter := center0302
  contactBall := contact0302
  work := work0302
  center_sq := center_sq0302
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0302.1
  jac_ok := checks0302.2.1
  accepted := checks0302.2.2

def tau0303 : RatBall :=
  ⟨⟨29/80, 1/80⟩, 3/160⟩
def center0303 : GaussianRat :=
  ⟨240695961/1000000000, 1905207/250000000⟩
def contact0303 : RatBall := localContactBall tau0303 center0303
def work0303 : RoundedTauEval :=
  evalTau precision tau0303 contact0303 logTwoBall

theorem center_sq0303 : (center0303.re : ℝ)^2 +
    (center0303.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0303]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0303 : work0303.theta.ok = true ∧
    work0303.jac.invOK = true ∧ acceptsUnitSq work0303.out = true := by decide +kernel

def cell0303 : CellCertificate where
  tauBall := tau0303
  contactCenter := center0303
  contactBall := contact0303
  work := work0303
  center_sq := center_sq0303
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0303.1
  jac_ok := checks0303.2.1
  accepted := checks0303.2.2

def cells : List CellCertificate := [cell0296, cell0297, cell0298, cell0299, cell0300, cell0301, cell0302, cell0303]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037


