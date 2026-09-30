-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:25:19.379433+00:00
-- url     : https://prove2.me/theorems/0de08b78-2904-4b05-a7e8-e3e3e9a7cae4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0057.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0057_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0461 : CellCertificate where
  tauBall := tau0461
  contactCenter := center0461
  contactBall := contact0461
  work := work0461
  center_sq := center_sq0461
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0461.1
  jac_ok := checks0461.2.1
  accepted := checks0461.2.2

def tau0462 : RatBall :=
  ⟨⟨-17/160, -43/160⟩, 3/320⟩
def center0462 : GaussianRat :=
  ⟨-39590143/500000000, -47162917/250000000⟩
def contact0462 : RatBall := localContactBall tau0462 center0462
def work0462 : RoundedTauEval :=
  evalTau precision tau0462 contact0462 logTwoBall

theorem center_sq0462 : (center0462.re : ℝ)^2 +
    (center0462.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0462]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0462 : work0462.theta.ok = true ∧
    work0462.jac.invOK = true ∧ acceptsUnitSq work0462.out = true := by decide +kernel

def cell0462 : CellCertificate where
  tauBall := tau0462
  contactCenter := center0462
  contactBall := contact0462
  work := work0462
  center_sq := center_sq0462
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0462.1
  jac_ok := checks0462.2.1
  accepted := checks0462.2.2

def tau0463 : RatBall :=
  ⟨⟨-19/160, -41/160⟩, 3/320⟩
def center0463 : GaussianRat :=
  ⟨-43873979/500000000, -35778323/200000000⟩
def contact0463 : RatBall := localContactBall tau0463 center0463
def work0463 : RoundedTauEval :=
  evalTau precision tau0463 contact0463 logTwoBall

theorem center_sq0463 : (center0463.re : ℝ)^2 +
    (center0463.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0463]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0463 : work0463.theta.ok = true ∧
    work0463.jac.invOK = true ∧ acceptsUnitSq work0463.out = true := by decide +kernel

def cell0463 : CellCertificate where
  tauBall := tau0463
  contactCenter := center0463
  contactBall := contact0463
  work := work0463
  center_sq := center_sq0463
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0463.1
  jac_ok := checks0463.2.1
  accepted := checks0463.2.2

def cells : List CellCertificate := [cell0456, cell0457, cell0458, cell0459, cell0460, cell0461, cell0462, cell0463]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057


