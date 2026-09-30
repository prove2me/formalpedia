-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:46:37.006628+00:00
-- url     : https://prove2.me/theorems/58be338c-d3a1-4819-9595-ef7f3d1c80cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0028.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0028_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0230 : RatBall := localContactBall tau0230 center0230
def work0230 : RoundedTauEval :=
  evalTau precision tau0230 contact0230 logTwoBall

theorem center_sq0230 : (center0230.re : ℝ)^2 +
    (center0230.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0230]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0230 : work0230.theta.ok = true ∧
    work0230.jac.invOK = true ∧ acceptsUnitSq work0230.out = true := by decide +kernel

def cell0230 : CellCertificate where
  tauBall := tau0230
  contactCenter := center0230
  contactBall := contact0230
  work := work0230
  center_sq := center_sq0230
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0230.1
  jac_ok := checks0230.2.1
  accepted := checks0230.2.2

def tau0231 : RatBall :=
  ⟨⟨-21/80, 13/80⟩, 3/160⟩
def center0231 : GaussianRat :=
  ⟨-4555953/25000000, 105764329/1000000000⟩
def contact0231 : RatBall := localContactBall tau0231 center0231
def work0231 : RoundedTauEval :=
  evalTau precision tau0231 contact0231 logTwoBall

theorem center_sq0231 : (center0231.re : ℝ)^2 +
    (center0231.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0231]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0231 : work0231.theta.ok = true ∧
    work0231.jac.invOK = true ∧ acceptsUnitSq work0231.out = true := by decide +kernel

def cell0231 : CellCertificate where
  tauBall := tau0231
  contactCenter := center0231
  contactBall := contact0231
  work := work0231
  center_sq := center_sq0231
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0231.1
  jac_ok := checks0231.2.1
  accepted := checks0231.2.2

def cells : List CellCertificate := [cell0224, cell0225, cell0226, cell0227, cell0228, cell0229, cell0230, cell0231]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028


