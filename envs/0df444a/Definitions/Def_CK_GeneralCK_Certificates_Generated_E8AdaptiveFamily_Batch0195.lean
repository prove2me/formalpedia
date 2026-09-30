-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0195
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0195
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:36:06.784226+00:00
-- url     : https://prove2.me/theorems/a5eb6c30-3bc5-4ed5-a2cf-8922e271df15
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0195.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0195_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1566 : GaussianRat :=
  ⟨22747453/1000000000, -270997951/1000000000⟩
def contact1566 : RatBall := localContactBall tau1566 center1566
def work1566 : RoundedTauEval :=
  evalTau precision tau1566 contact1566 logTwoBall

theorem center_sq1566 : (center1566.re : ℝ)^2 +
    (center1566.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1566]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1566 : work1566.theta.ok = true ∧
    work1566.jac.invOK = true ∧ acceptsUnitSq work1566.out = true := by decide +kernel

def cell1566 : CellCertificate where
  tauBall := tau1566
  contactCenter := center1566
  contactBall := contact1566
  work := work1566
  center_sq := center_sq1566
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1566.1
  jac_ok := checks1566.2.1
  accepted := checks1566.2.2

def tau1567 : RatBall :=
  ⟨⟨11/320, -119/320⟩, 3/640⟩
def center1567 : GaussianRat :=
  ⟨27795199/1000000000, -135428181/500000000⟩
def contact1567 : RatBall := localContactBall tau1567 center1567
def work1567 : RoundedTauEval :=
  evalTau precision tau1567 contact1567 logTwoBall

theorem center_sq1567 : (center1567.re : ℝ)^2 +
    (center1567.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1567]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1567 : work1567.theta.ok = true ∧
    work1567.jac.invOK = true ∧ acceptsUnitSq work1567.out = true := by decide +kernel

def cell1567 : CellCertificate where
  tauBall := tau1567
  contactCenter := center1567
  contactBall := contact1567
  work := work1567
  center_sq := center_sq1567
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1567.1
  jac_ok := checks1567.2.1
  accepted := checks1567.2.2

def cells : List CellCertificate := [cell1560, cell1561, cell1562, cell1563, cell1564, cell1565, cell1566, cell1567]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195


