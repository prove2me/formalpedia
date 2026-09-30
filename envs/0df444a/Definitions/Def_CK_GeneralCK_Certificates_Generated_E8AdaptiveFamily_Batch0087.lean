-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:25:19.58564+00:00
-- url     : https://prove2.me/theorems/7b888861-7c4e-4fdd-a161-8f636110e00d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0087.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0087_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0702 : RatBall :=
  ⟨⟨43/160, -29/160⟩, 3/320⟩
def center0702 : GaussianRat :=
  ⟨187487239/1000000000, -23550431/200000000⟩
def contact0702 : RatBall := localContactBall tau0702 center0702
def work0702 : RoundedTauEval :=
  evalTau precision tau0702 contact0702 logTwoBall

theorem center_sq0702 : (center0702.re : ℝ)^2 +
    (center0702.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0702 : work0702.theta.ok = true ∧
    work0702.jac.invOK = true ∧ acceptsUnitSq work0702.out = true := by decide +kernel

def cell0702 : CellCertificate where
  tauBall := tau0702
  contactCenter := center0702
  contactBall := contact0702
  work := work0702
  center_sq := center_sq0702
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0702.1
  jac_ok := checks0702.2.1
  accepted := checks0702.2.2

def tau0703 : RatBall :=
  ⟨⟨9/32, -31/160⟩, 3/320⟩
def center0703 : GaussianRat :=
  ⟨19656377/100000000, -125132383/1000000000⟩
def contact0703 : RatBall := localContactBall tau0703 center0703
def work0703 : RoundedTauEval :=
  evalTau precision tau0703 contact0703 logTwoBall

theorem center_sq0703 : (center0703.re : ℝ)^2 +
    (center0703.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0703]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0703 : work0703.theta.ok = true ∧
    work0703.jac.invOK = true ∧ acceptsUnitSq work0703.out = true := by decide +kernel

def cell0703 : CellCertificate where
  tauBall := tau0703
  contactCenter := center0703
  contactBall := contact0703
  work := work0703
  center_sq := center_sq0703
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0703.1
  jac_ok := checks0703.2.1
  accepted := checks0703.2.2

def cells : List CellCertificate := [cell0696, cell0697, cell0698, cell0699, cell0700, cell0701, cell0702, cell0703]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087


