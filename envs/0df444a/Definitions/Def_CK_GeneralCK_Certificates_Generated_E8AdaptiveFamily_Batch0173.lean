-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:16:38.954993+00:00
-- url     : https://prove2.me/theorems/7bb5cd01-99e2-4672-91c5-c9da0c0572ed
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0173.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0173_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1389 : CellCertificate where
  tauBall := tau1389
  contactCenter := center1389
  contactBall := contact1389
  work := work1389
  center_sq := center_sq1389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1389.1
  jac_ok := checks1389.2.1
  accepted := checks1389.2.2

def tau1390 : RatBall :=
  ⟨⟨-11/64, -21/64⟩, 3/640⟩
def center1390 : GaussianRat :=
  ⟨-65949739/500000000, -57017591/250000000⟩
def contact1390 : RatBall := localContactBall tau1390 center1390
def work1390 : RoundedTauEval :=
  evalTau precision tau1390 contact1390 logTwoBall

theorem center_sq1390 : (center1390.re : ℝ)^2 +
    (center1390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1390 : work1390.theta.ok = true ∧
    work1390.jac.invOK = true ∧ acceptsUnitSq work1390.out = true := by decide +kernel

def cell1390 : CellCertificate where
  tauBall := tau1390
  contactCenter := center1390
  contactBall := contact1390
  work := work1390
  center_sq := center_sq1390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1390.1
  jac_ok := checks1390.2.1
  accepted := checks1390.2.2

def tau1391 : RatBall :=
  ⟨⟨-53/320, -21/64⟩, 3/640⟩
def center1391 : GaussianRat :=
  ⟨-127250921/1000000000, -228652029/1000000000⟩
def contact1391 : RatBall := localContactBall tau1391 center1391
def work1391 : RoundedTauEval :=
  evalTau precision tau1391 contact1391 logTwoBall

theorem center_sq1391 : (center1391.re : ℝ)^2 +
    (center1391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1391 : work1391.theta.ok = true ∧
    work1391.jac.invOK = true ∧ acceptsUnitSq work1391.out = true := by decide +kernel

def cell1391 : CellCertificate where
  tauBall := tau1391
  contactCenter := center1391
  contactBall := contact1391
  work := work1391
  center_sq := center_sq1391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1391.1
  jac_ok := checks1391.2.1
  accepted := checks1391.2.2

def cells : List CellCertificate := [cell1384, cell1385, cell1386, cell1387, cell1388, cell1389, cell1390, cell1391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173


