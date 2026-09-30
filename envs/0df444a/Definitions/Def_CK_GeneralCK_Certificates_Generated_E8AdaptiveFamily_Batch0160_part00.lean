-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0160_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:06:45.743807+00:00
-- url     : https://prove2.me/theorems/e380f647-cfc7-410f-b172-20890d8f3966
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160 (part 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0160 (part 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1280 : RatBall :=
  ⟨⟨-83/320, -19/64⟩, 3/640⟩
def center1280 : GaussianRat :=
  ⟨-191313683/1000000000, -3929501/20000000⟩
def contact1280 : RatBall := localContactBall tau1280 center1280
def work1280 : RoundedTauEval :=
  evalTau precision tau1280 contact1280 logTwoBall

theorem center_sq1280 : (center1280.re : ℝ)^2 +
    (center1280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1280 : work1280.theta.ok = true ∧
    work1280.jac.invOK = true ∧ acceptsUnitSq work1280.out = true := by decide +kernel

def cell1280 : CellCertificate where
  tauBall := tau1280
  contactCenter := center1280
  contactBall := contact1280
  work := work1280
  center_sq := center_sq1280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1280.1
  jac_ok := checks1280.2.1
  accepted := checks1280.2.2

def tau1281 : RatBall :=
  ⟨⟨-81/320, -19/64⟩, 3/640⟩
def center1281 : GaussianRat :=
  ⟨-186989333/1000000000, -49293783/250000000⟩
def contact1281 : RatBall := localContactBall tau1281 center1281
def work1281 : RoundedTauEval :=
  evalTau precision tau1281 contact1281 logTwoBall

theorem center_sq1281 : (center1281.re : ℝ)^2 +
    (center1281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1281 : work1281.theta.ok = true ∧
    work1281.jac.invOK = true ∧ acceptsUnitSq work1281.out = true := by decide +kernel

def cell1281 : CellCertificate where
  tauBall := tau1281
  contactCenter := center1281
  contactBall := contact1281
  work := work1281
  center_sq := center_sq1281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1281.1
  jac_ok := checks1281.2.1
  accepted := checks1281.2.2

def tau1282 : RatBall :=
  ⟨⟨-83/320, -93/320⟩, 3/640⟩
def center1282 : GaussianRat :=
  ⟨-95308733/500000000, -192166077/1000000000⟩
def contact1282 : RatBall := localContactBall tau1282 center1282
def work1282 : RoundedTauEval :=
  evalTau precision tau1282 contact1282 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160


