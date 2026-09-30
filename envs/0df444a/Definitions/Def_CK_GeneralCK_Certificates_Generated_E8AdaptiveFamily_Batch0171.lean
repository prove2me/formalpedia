-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:44:22.660658+00:00
-- url     : https://prove2.me/theorems/f924d044-49d4-431c-8d5f-130d6b401992
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0171.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0171_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1374 : work1374.theta.ok = true ∧
    work1374.jac.invOK = true ∧ acceptsUnitSq work1374.out = true := by decide +kernel

def cell1374 : CellCertificate where
  tauBall := tau1374
  contactCenter := center1374
  contactBall := contact1374
  work := work1374
  center_sq := center_sq1374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1374.1
  jac_ok := checks1374.2.1
  accepted := checks1374.2.2

def tau1375 : RatBall :=
  ⟨⟨-61/320, -21/64⟩, 3/640⟩
def center1375 : GaussianRat :=
  ⟨-145746161/1000000000, -113109273/500000000⟩
def contact1375 : RatBall := localContactBall tau1375 center1375
def work1375 : RoundedTauEval :=
  evalTau precision tau1375 contact1375 logTwoBall

theorem center_sq1375 : (center1375.re : ℝ)^2 +
    (center1375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1375 : work1375.theta.ok = true ∧
    work1375.jac.invOK = true ∧ acceptsUnitSq work1375.out = true := by decide +kernel

def cell1375 : CellCertificate where
  tauBall := tau1375
  contactCenter := center1375
  contactBall := contact1375
  work := work1375
  center_sq := center_sq1375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1375.1
  jac_ok := checks1375.2.1
  accepted := checks1375.2.2

def cells : List CellCertificate := [cell1368, cell1369, cell1370, cell1371, cell1372, cell1373, cell1374, cell1375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171


