-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:45.729042+00:00
-- url     : https://prove2.me/theorems/54d13d97-10ad-493b-9846-c60b2cedfdb3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0115.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0926 : (center0926.re : ℝ)^2 +
    (center0926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0926 : work0926.theta.ok = true ∧
    work0926.jac.invOK = true ∧ acceptsUnitSq work0926.out = true := by decide +kernel

def cell0926 : CellCertificate where
  tauBall := tau0926
  contactCenter := center0926
  contactBall := contact0926
  work := work0926
  center_sq := center_sq0926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0926.1
  jac_ok := checks0926.2.1
  accepted := checks0926.2.2

def tau0927 : RatBall :=
  ⟨⟨-17/160, 41/160⟩, 3/320⟩
def center0927 : GaussianRat :=
  ⟨-1572299/20000000, 179469913/1000000000⟩
def contact0927 : RatBall := localContactBall tau0927 center0927
def work0927 : RoundedTauEval :=
  evalTau precision tau0927 contact0927 logTwoBall

theorem center_sq0927 : (center0927.re : ℝ)^2 +
    (center0927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0927]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0927 : work0927.theta.ok = true ∧
    work0927.jac.invOK = true ∧ acceptsUnitSq work0927.out = true := by decide +kernel

def cell0927 : CellCertificate where
  tauBall := tau0927
  contactCenter := center0927
  contactBall := contact0927
  work := work0927
  center_sq := center_sq0927
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0927.1
  jac_ok := checks0927.2.1
  accepted := checks0927.2.2

def cells : List CellCertificate := [cell0920, cell0921, cell0922, cell0923, cell0924, cell0925, cell0926, cell0927]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115


