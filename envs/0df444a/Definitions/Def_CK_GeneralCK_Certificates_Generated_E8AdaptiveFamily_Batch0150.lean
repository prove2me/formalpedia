-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:24:19.596847+00:00
-- url     : https://prove2.me/theorems/628f9b7e-4149-465c-90bf-548cf2658519
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0150.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0150_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1206 : RoundedTauEval :=
  evalTau precision tau1206 contact1206 logTwoBall

theorem center_sq1206 : (center1206.re : ℝ)^2 +
    (center1206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1206 : work1206.theta.ok = true ∧
    work1206.jac.invOK = true ∧ acceptsUnitSq work1206.out = true := by decide +kernel

def cell1206 : CellCertificate where
  tauBall := tau1206
  contactCenter := center1206
  contactBall := contact1206
  work := work1206
  center_sq := center_sq1206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1206.1
  jac_ok := checks1206.2.1
  accepted := checks1206.2.2

def tau1207 : RatBall :=
  ⟨⟨-71/320, -21/64⟩, 3/640⟩
def center1207 : GaussianRat :=
  ⟨-168468823/1000000000, -55699379/250000000⟩
def contact1207 : RatBall := localContactBall tau1207 center1207
def work1207 : RoundedTauEval :=
  evalTau precision tau1207 contact1207 logTwoBall

theorem center_sq1207 : (center1207.re : ℝ)^2 +
    (center1207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1207 : work1207.theta.ok = true ∧
    work1207.jac.invOK = true ∧ acceptsUnitSq work1207.out = true := by decide +kernel

def cell1207 : CellCertificate where
  tauBall := tau1207
  contactCenter := center1207
  contactBall := contact1207
  work := work1207
  center_sq := center_sq1207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1207.1
  jac_ok := checks1207.2.1
  accepted := checks1207.2.2

def cells : List CellCertificate := [cell1200, cell1201, cell1202, cell1203, cell1204, cell1205, cell1206, cell1207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150


