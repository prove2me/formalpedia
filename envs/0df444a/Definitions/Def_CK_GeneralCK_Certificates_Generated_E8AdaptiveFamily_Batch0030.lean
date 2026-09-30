-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:16:48.663838+00:00
-- url     : https://prove2.me/theorems/b27aaf12-3016-4e4e-be13-7cf1d9c8c6d6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0030.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0246 : RatBall := localContactBall tau0246 center0246
def work0246 : RoundedTauEval :=
  evalTau precision tau0246 contact0246 logTwoBall

theorem center_sq0246 : (center0246.re : ℝ)^2 +
    (center0246.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0246]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0246 : work0246.theta.ok = true ∧
    work0246.jac.invOK = true ∧ acceptsUnitSq work0246.out = true := by decide +kernel

def cell0246 : CellCertificate where
  tauBall := tau0246
  contactCenter := center0246
  contactBall := contact0246
  work := work0246
  center_sq := center_sq0246
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0246.1
  jac_ok := checks0246.2.1
  accepted := checks0246.2.2

def tau0247 : RatBall :=
  ⟨⟨-7/80, 13/80⟩, 3/160⟩
def center0247 : GaussianRat :=
  ⟨-31086987/500000000, 112745169/1000000000⟩
def contact0247 : RatBall := localContactBall tau0247 center0247
def work0247 : RoundedTauEval :=
  evalTau precision tau0247 contact0247 logTwoBall

theorem center_sq0247 : (center0247.re : ℝ)^2 +
    (center0247.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0247]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0247 : work0247.theta.ok = true ∧
    work0247.jac.invOK = true ∧ acceptsUnitSq work0247.out = true := by decide +kernel

def cell0247 : CellCertificate where
  tauBall := tau0247
  contactCenter := center0247
  contactBall := contact0247
  work := work0247
  center_sq := center_sq0247
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0247.1
  jac_ok := checks0247.2.1
  accepted := checks0247.2.2

def cells : List CellCertificate := [cell0240, cell0241, cell0242, cell0243, cell0244, cell0245, cell0246, cell0247]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030


