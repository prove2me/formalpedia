-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:26:06.44595+00:00
-- url     : https://prove2.me/theorems/25dd4dd9-1e01-47cb-a9fb-2ad72507b4cb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0009.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0009_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0078 : work0078.theta.ok = true ∧
    work0078.jac.invOK = true ∧ acceptsUnitSq work0078.out = true := by decide +kernel

def cell0078 : CellCertificate where
  tauBall := tau0078
  contactCenter := center0078
  contactBall := contact0078
  work := work0078
  center_sq := center_sq0078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0078.1
  jac_ok := checks0078.2.1
  accepted := checks0078.2.2

def tau0079 : RatBall :=
  ⟨⟨-23/80, -9/80⟩, 3/160⟩
def center0079 : GaussianRat :=
  ⟨-196096551/1000000000, -71999991/1000000000⟩
def contact0079 : RatBall := localContactBall tau0079 center0079
def work0079 : RoundedTauEval :=
  evalTau precision tau0079 contact0079 logTwoBall

theorem center_sq0079 : (center0079.re : ℝ)^2 +
    (center0079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0079 : work0079.theta.ok = true ∧
    work0079.jac.invOK = true ∧ acceptsUnitSq work0079.out = true := by decide +kernel

def cell0079 : CellCertificate where
  tauBall := tau0079
  contactCenter := center0079
  contactBall := contact0079
  work := work0079
  center_sq := center_sq0079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0079.1
  jac_ok := checks0079.2.1
  accepted := checks0079.2.2

def cells : List CellCertificate := [cell0072, cell0073, cell0074, cell0075, cell0076, cell0077, cell0078, cell0079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009


