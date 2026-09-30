-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:42.927105+00:00
-- url     : https://prove2.me/theorems/4f70a3e7-5d0f-457f-84a3-fd9a74ca21dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0187 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq1498 : (center1498.re : ℝ)^2 +
    (center1498.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1498]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1498 : work1498.theta.ok = true ∧
    work1498.jac.invOK = true ∧ acceptsUnitSq work1498.out = true := by decide +kernel

def cell1498 : CellCertificate where
  tauBall := tau1498
  contactCenter := center1498
  contactBall := contact1498
  work := work1498
  center_sq := center_sq1498
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1498.1
  jac_ok := checks1498.2.1
  accepted := checks1498.2.2

def tau1499 : RatBall :=
  ⟨⟨-1/320, -121/320⟩, 3/640⟩
def center1499 : GaussianRat :=
  ⟨-2543217/1000000000, -276353553/1000000000⟩
def contact1499 : RatBall := localContactBall tau1499 center1499
def work1499 : RoundedTauEval :=
  evalTau precision tau1499 contact1499 logTwoBall

theorem center_sq1499 : (center1499.re : ℝ)^2 +
    (center1499.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1499 : work1499.theta.ok = true ∧
    work1499.jac.invOK = true ∧ acceptsUnitSq work1499.out = true := by decide +kernel

def cell1499 : CellCertificate where
  tauBall := tau1499
  contactCenter := center1499
  contactBall := contact1499
  work := work1499
  center_sq := center_sq1499
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1499.1
  jac_ok := checks1499.2.1
  accepted := checks1499.2.2

def tau1500 : RatBall :=
  ⟨⟨-3/64, -119/320⟩, 3/640⟩
def center1500 : GaussianRat :=
  ⟨-18938457/500000000, -5409781/20000000⟩
def contact1500 : RatBall := localContactBall tau1500 center1500
def work1500 : RoundedTauEval :=
  evalTau precision tau1500 contact1500 logTwoBall

theorem center_sq1500 : (center1500.re : ℝ)^2 +
    (center1500.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1500 : work1500.theta.ok = true ∧
    work1500.jac.invOK = true ∧ acceptsUnitSq work1500.out = true := by decide +kernel

def cell1500 : CellCertificate where
  tauBall := tau1500
  contactCenter := center1500
  contactBall := contact1500
  work := work1500
  center_sq := center_sq1500
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1500.1
  jac_ok := checks1500.2.1
  accepted := checks1500.2.2

def tau1501 : RatBall :=
  ⟨⟨-13/320, -119/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187


