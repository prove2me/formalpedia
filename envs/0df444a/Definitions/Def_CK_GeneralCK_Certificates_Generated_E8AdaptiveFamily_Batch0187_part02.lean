-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part02
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:57:30.912078+00:00
-- url     : https://prove2.me/theorems/93d20023-58f6-48f5-b3d1-6820e5ee3e3c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187 (part 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0187 (part 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0187_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1501 : GaussianRat :=
  ⟨-32838611/1000000000, -135343343/500000000⟩
def contact1501 : RatBall := localContactBall tau1501 center1501
def work1501 : RoundedTauEval :=
  evalTau precision tau1501 contact1501 logTwoBall

theorem center_sq1501 : (center1501.re : ℝ)^2 +
    (center1501.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1501]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1501 : work1501.theta.ok = true ∧
    work1501.jac.invOK = true ∧ acceptsUnitSq work1501.out = true := by decide +kernel

def cell1501 : CellCertificate where
  tauBall := tau1501
  contactCenter := center1501
  contactBall := contact1501
  work := work1501
  center_sq := center_sq1501
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1501.1
  jac_ok := checks1501.2.1
  accepted := checks1501.2.2

def tau1502 : RatBall :=
  ⟨⟨-3/64, -117/320⟩, 3/640⟩
def center1502 : GaussianRat :=
  ⟨-18834129/500000000, -13273367/50000000⟩
def contact1502 : RatBall := localContactBall tau1502 center1502
def work1502 : RoundedTauEval :=
  evalTau precision tau1502 contact1502 logTwoBall

theorem center_sq1502 : (center1502.re : ℝ)^2 +
    (center1502.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1502]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1502 : work1502.theta.ok = true ∧
    work1502.jac.invOK = true ∧ acceptsUnitSq work1502.out = true := by decide +kernel

def cell1502 : CellCertificate where
  tauBall := tau1502
  contactCenter := center1502
  contactBall := contact1502
  work := work1502
  center_sq := center_sq1502
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1502.1
  jac_ok := checks1502.2.1
  accepted := checks1502.2.2

def tau1503 : RatBall :=
  ⟨⟨-13/320, -117/320⟩, 3/640⟩
def center1503 : GaussianRat :=
  ⟨-6531493/200000000, -265659553/1000000000⟩
def contact1503 : RatBall := localContactBall tau1503 center1503
def work1503 : RoundedTauEval :=
  evalTau precision tau1503 contact1503 logTwoBall

theorem center_sq1503 : (center1503.re : ℝ)^2 +
    (center1503.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1503]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187


