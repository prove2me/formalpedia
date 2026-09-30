-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0098
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0098
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:55:48.925794+00:00
-- url     : https://prove2.me/theorems/9fce834e-e1fd-4a89-a097-3d2af7f7646a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0098.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0098_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0790 : (center0790.re : ℝ)^2 +
    (center0790.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0790]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0790 : work0790.theta.ok = true ∧
    work0790.jac.invOK = true ∧ acceptsUnitSq work0790.out = true := by decide +kernel

def cell0790 : CellCertificate where
  tauBall := tau0790
  contactCenter := center0790
  contactBall := contact0790
  work := work0790
  center_sq := center_sq0790
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0790.1
  jac_ok := checks0790.2.1
  accepted := checks0790.2.2

def tau0791 : RatBall :=
  ⟨⟨-57/160, 17/160⟩, 3/320⟩
def center0791 : GaussianRat :=
  ⟨-119567729/500000000, 32582953/500000000⟩
def contact0791 : RatBall := localContactBall tau0791 center0791
def work0791 : RoundedTauEval :=
  evalTau precision tau0791 contact0791 logTwoBall

theorem center_sq0791 : (center0791.re : ℝ)^2 +
    (center0791.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0791]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0791 : work0791.theta.ok = true ∧
    work0791.jac.invOK = true ∧ acceptsUnitSq work0791.out = true := by decide +kernel

def cell0791 : CellCertificate where
  tauBall := tau0791
  contactCenter := center0791
  contactBall := contact0791
  work := work0791
  center_sq := center_sq0791
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0791.1
  jac_ok := checks0791.2.1
  accepted := checks0791.2.2

def cells : List CellCertificate := [cell0784, cell0785, cell0786, cell0787, cell0788, cell0789, cell0790, cell0791]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098


