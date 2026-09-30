-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:23:42.911815+00:00
-- url     : https://prove2.me/theorems/e1090d80-6684-426d-915b-a62e3e061212
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0088.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0088_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0710 : (center0710.re : ℝ)^2 +
    (center0710.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0710]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0710 : work0710.theta.ok = true ∧
    work0710.jac.invOK = true ∧ acceptsUnitSq work0710.out = true := by decide +kernel

def cell0710 : CellCertificate where
  tauBall := tau0710
  contactCenter := center0710
  contactBall := contact0710
  work := work0710
  center_sq := center_sq0710
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0710.1
  jac_ok := checks0710.2.1
  accepted := checks0710.2.2

def tau0711 : RatBall :=
  ⟨⟨49/160, -31/160⟩, 3/320⟩
def center0711 : GaussianRat :=
  ⟨106425859/500000000, -123294587/1000000000⟩
def contact0711 : RatBall := localContactBall tau0711 center0711
def work0711 : RoundedTauEval :=
  evalTau precision tau0711 contact0711 logTwoBall

theorem center_sq0711 : (center0711.re : ℝ)^2 +
    (center0711.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0711]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0711 : work0711.theta.ok = true ∧
    work0711.jac.invOK = true ∧ acceptsUnitSq work0711.out = true := by decide +kernel

def cell0711 : CellCertificate where
  tauBall := tau0711
  contactCenter := center0711
  contactBall := contact0711
  work := work0711
  center_sq := center_sq0711
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0711.1
  jac_ok := checks0711.2.1
  accepted := checks0711.2.2

def cells : List CellCertificate := [cell0704, cell0705, cell0706, cell0707, cell0708, cell0709, cell0710, cell0711]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088


