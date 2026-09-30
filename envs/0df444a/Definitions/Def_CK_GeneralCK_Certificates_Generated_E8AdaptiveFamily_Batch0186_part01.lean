-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:13:48.908313+00:00
-- url     : https://prove2.me/theorems/112f50b0-f8c2-45d9-8abc-f9595dbb3bf6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0186 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0186_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1490 : (center1490.re : ℝ)^2 +
    (center1490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1490 : work1490.theta.ok = true ∧
    work1490.jac.invOK = true ∧ acceptsUnitSq work1490.out = true := by decide +kernel

def cell1490 : CellCertificate where
  tauBall := tau1490
  contactCenter := center1490
  contactBall := contact1490
  work := work1490
  center_sq := center_sq1490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1490.1
  jac_ok := checks1490.2.1
  accepted := checks1490.2.2

def tau1491 : RatBall :=
  ⟨⟨-9/320, -121/320⟩, 3/640⟩
def center1491 : GaussianRat :=
  ⟨-4575351/200000000, -276061831/1000000000⟩
def contact1491 : RatBall := localContactBall tau1491 center1491
def work1491 : RoundedTauEval :=
  evalTau precision tau1491 contact1491 logTwoBall

theorem center_sq1491 : (center1491.re : ℝ)^2 +
    (center1491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1491 : work1491.theta.ok = true ∧
    work1491.jac.invOK = true ∧ acceptsUnitSq work1491.out = true := by decide +kernel

def cell1491 : CellCertificate where
  tauBall := tau1491
  contactCenter := center1491
  contactBall := contact1491
  work := work1491
  center_sq := center_sq1491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1491.1
  jac_ok := checks1491.2.1
  accepted := checks1491.2.2

def tau1492 : RatBall :=
  ⟨⟨-7/320, -123/320⟩, 3/640⟩
def center1492 : GaussianRat :=
  ⟨-3580067/200000000, -8789831/31250000⟩
def contact1492 : RatBall := localContactBall tau1492 center1492
def work1492 : RoundedTauEval :=
  evalTau precision tau1492 contact1492 logTwoBall

theorem center_sq1492 : (center1492.re : ℝ)^2 +
    (center1492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1492 : work1492.theta.ok = true ∧
    work1492.jac.invOK = true ∧ acceptsUnitSq work1492.out = true := by decide +kernel

def cell1492 : CellCertificate where
  tauBall := tau1492
  contactCenter := center1492
  contactBall := contact1492
  work := work1492
  center_sq := center_sq1492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1492.1
  jac_ok := checks1492.2.1
  accepted := checks1492.2.2

def tau1493 : RatBall :=
  ⟨⟨-1/64, -123/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186


