-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:09:25.669736+00:00
-- url     : https://prove2.me/theorems/a14651a9-e8a2-4ca4-873b-b216395febef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0038.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0038_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0310 : (center0310.re : ℝ)^2 +
    (center0310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0310 : work0310.theta.ok = true ∧
    work0310.jac.invOK = true ∧ acceptsUnitSq work0310.out = true := by decide +kernel

def cell0310 : CellCertificate where
  tauBall := tau0310
  contactCenter := center0310
  contactBall := contact0310
  work := work0310
  center_sq := center_sq0310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0310.1
  jac_ok := checks0310.2.1
  accepted := checks0310.2.2

def tau0311 : RatBall :=
  ⟨⟨17/80, 9/80⟩, 3/160⟩
def center0311 : GaussianRat :=
  ⟨29368329/200000000, 18684497/250000000⟩
def contact0311 : RatBall := localContactBall tau0311 center0311
def work0311 : RoundedTauEval :=
  evalTau precision tau0311 contact0311 logTwoBall

theorem center_sq0311 : (center0311.re : ℝ)^2 +
    (center0311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0311 : work0311.theta.ok = true ∧
    work0311.jac.invOK = true ∧ acceptsUnitSq work0311.out = true := by decide +kernel

def cell0311 : CellCertificate where
  tauBall := tau0311
  contactCenter := center0311
  contactBall := contact0311
  work := work0311
  center_sq := center_sq0311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0311.1
  jac_ok := checks0311.2.1
  accepted := checks0311.2.2

def cells : List CellCertificate := [cell0304, cell0305, cell0306, cell0307, cell0308, cell0309, cell0310, cell0311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038


