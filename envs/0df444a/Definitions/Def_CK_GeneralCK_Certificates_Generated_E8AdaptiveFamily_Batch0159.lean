-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:55:34.439741+00:00
-- url     : https://prove2.me/theorems/028d5ea7-fe26-41c2-9efd-2c16a1250885
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0159.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1277 : (center1277.re : ℝ)^2 +
    (center1277.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1277]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1277 : work1277.theta.ok = true ∧
    work1277.jac.invOK = true ∧ acceptsUnitSq work1277.out = true := by decide +kernel

def cell1277 : CellCertificate where
  tauBall := tau1277
  contactCenter := center1277
  contactBall := contact1277
  work := work1277
  center_sq := center_sq1277
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1277.1
  jac_ok := checks1277.2.1
  accepted := checks1277.2.2

def tau1278 : RatBall :=
  ⟨⟨-87/320, -93/320⟩, 3/640⟩
def center1278 : GaussianRat :=
  ⟨-2489819/12500000, -47692707/250000000⟩
def contact1278 : RatBall := localContactBall tau1278 center1278
def work1278 : RoundedTauEval :=
  evalTau precision tau1278 contact1278 logTwoBall

theorem center_sq1278 : (center1278.re : ℝ)^2 +
    (center1278.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1278]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1278 : work1278.theta.ok = true ∧
    work1278.jac.invOK = true ∧ acceptsUnitSq work1278.out = true := by decide +kernel

def cell1278 : CellCertificate where
  tauBall := tau1278
  contactCenter := center1278
  contactBall := contact1278
  work := work1278
  center_sq := center_sq1278
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1278.1
  jac_ok := checks1278.2.1
  accepted := checks1278.2.2

def tau1279 : RatBall :=
  ⟨⟨-17/64, -93/320⟩, 3/640⟩
def center1279 : GaussianRat :=
  ⟨-97455589/500000000, -191473909/1000000000⟩
def contact1279 : RatBall := localContactBall tau1279 center1279
def work1279 : RoundedTauEval :=
  evalTau precision tau1279 contact1279 logTwoBall

theorem center_sq1279 : (center1279.re : ℝ)^2 +
    (center1279.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1279]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1279 : work1279.theta.ok = true ∧
    work1279.jac.invOK = true ∧ acceptsUnitSq work1279.out = true := by decide +kernel

def cell1279 : CellCertificate where
  tauBall := tau1279
  contactCenter := center1279
  contactBall := contact1279
  work := work1279
  center_sq := center_sq1279
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1279.1
  jac_ok := checks1279.2.1
  accepted := checks1279.2.2

def cells : List CellCertificate := [cell1272, cell1273, cell1274, cell1275, cell1276, cell1277, cell1278, cell1279]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159


