-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0189_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:10:37.836089+00:00
-- url     : https://prove2.me/theorems/91874d69-6fb9-4f15-abb7-8ad335a7a1e2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0189 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1512 : RatBall :=
  ⟨⟨-11/320, -23/64⟩, 3/640⟩
def center1512 : GaussianRat :=
  ⟨-27492413/1000000000, -2037657/7812500⟩
def contact1512 : RatBall := localContactBall tau1512 center1512
def work1512 : RoundedTauEval :=
  evalTau precision tau1512 contact1512 logTwoBall

theorem center_sq1512 : (center1512.re : ℝ)^2 +
    (center1512.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1512]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1512 : work1512.theta.ok = true ∧
    work1512.jac.invOK = true ∧ acceptsUnitSq work1512.out = true := by decide +kernel

def cell1512 : CellCertificate where
  tauBall := tau1512
  contactCenter := center1512
  contactBall := contact1512
  work := work1512
  center_sq := center_sq1512
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1512.1
  jac_ok := checks1512.2.1
  accepted := checks1512.2.2

def tau1513 : RatBall :=
  ⟨⟨-9/320, -23/64⟩, 3/640⟩
def center1513 : GaussianRat :=
  ⟨-22499417/1000000000, -260954001/1000000000⟩
def contact1513 : RatBall := localContactBall tau1513 center1513
def work1513 : RoundedTauEval :=
  evalTau precision tau1513 contact1513 logTwoBall

theorem center_sq1513 : (center1513.re : ℝ)^2 +
    (center1513.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1513]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1513 : work1513.theta.ok = true ∧
    work1513.jac.invOK = true ∧ acceptsUnitSq work1513.out = true := by decide +kernel

def cell1513 : CellCertificate where
  tauBall := tau1513
  contactCenter := center1513
  contactBall := contact1513
  work := work1513
  center_sq := center_sq1513
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1513.1
  jac_ok := checks1513.2.1
  accepted := checks1513.2.2

def tau1514 : RatBall :=
  ⟨⟨-11/320, -113/320⟩, 3/640⟩
def center1514 : GaussianRat :=
  ⟨-5469449/200000000, -51168439/200000000⟩
def contact1514 : RatBall := localContactBall tau1514 center1514

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189


