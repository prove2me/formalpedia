-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:51:24.547694+00:00
-- url     : https://prove2.me/theorems/d24fcb55-8389-41ee-8293-54ab98880c67
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0186 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1493 : GaussianRat :=
  ⟨-12788043/1000000000, -281364591/1000000000⟩
def contact1493 : RatBall := localContactBall tau1493 center1493
def work1493 : RoundedTauEval :=
  evalTau precision tau1493 contact1493 logTwoBall

theorem center_sq1493 : (center1493.re : ℝ)^2 +
    (center1493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1493 : work1493.theta.ok = true ∧
    work1493.jac.invOK = true ∧ acceptsUnitSq work1493.out = true := by decide +kernel

def cell1493 : CellCertificate where
  tauBall := tau1493
  contactCenter := center1493
  contactBall := contact1493
  work := work1493
  center_sq := center_sq1493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1493.1
  jac_ok := checks1493.2.1
  accepted := checks1493.2.2

def tau1494 : RatBall :=
  ⟨⟨-7/320, -121/320⟩, 3/640⟩
def center1494 : GaussianRat :=
  ⟨-2224603/125000000, -539411/1953125⟩
def contact1494 : RatBall := localContactBall tau1494 center1494
def work1494 : RoundedTauEval :=
  evalTau precision tau1494 contact1494 logTwoBall

theorem center_sq1494 : (center1494.re : ℝ)^2 +
    (center1494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1494 : work1494.theta.ok = true ∧
    work1494.jac.invOK = true ∧ acceptsUnitSq work1494.out = true := by decide +kernel

def cell1494 : CellCertificate where
  tauBall := tau1494
  contactCenter := center1494
  contactBall := contact1494
  work := work1494
  center_sq := center_sq1494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1494.1
  jac_ok := checks1494.2.1
  accepted := checks1494.2.2

def tau1495 : RatBall :=
  ⟨⟨-1/64, -121/320⟩, 3/640⟩
def center1495 : GaussianRat :=
  ⟨-254281/20000000, -276265959/1000000000⟩
def contact1495 : RatBall := localContactBall tau1495 center1495
def work1495 : RoundedTauEval :=
  evalTau precision tau1495 contact1495 logTwoBall

theorem center_sq1495 : (center1495.re : ℝ)^2 +
    (center1495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1495]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186


