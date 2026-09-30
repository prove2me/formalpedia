-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0196
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0196
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:02:23.520674+00:00
-- url     : https://prove2.me/theorems/2be2c363-a17c-4063-84b1-c9070c15e474
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0196.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0196_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact1573 : RatBall := localContactBall tau1573 center1573
def work1573 : RoundedTauEval :=
  evalTau precision tau1573 contact1573 logTwoBall

theorem center_sq1573 : (center1573.re : ℝ)^2 +
    (center1573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1573 : work1573.theta.ok = true ∧
    work1573.jac.invOK = true ∧ acceptsUnitSq work1573.out = true := by decide +kernel

def cell1573 : CellCertificate where
  tauBall := tau1573
  contactCenter := center1573
  contactBall := contact1573
  work := work1573
  center_sq := center_sq1573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1573.1
  jac_ok := checks1573.2.1
  accepted := checks1573.2.2

def tau1574 : RatBall :=
  ⟨⟨9/320, -23/64⟩, 3/640⟩
def center1574 : GaussianRat :=
  ⟨22499417/1000000000, -260954001/1000000000⟩
def contact1574 : RatBall := localContactBall tau1574 center1574
def work1574 : RoundedTauEval :=
  evalTau precision tau1574 contact1574 logTwoBall

theorem center_sq1574 : (center1574.re : ℝ)^2 +
    (center1574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1574 : work1574.theta.ok = true ∧
    work1574.jac.invOK = true ∧ acceptsUnitSq work1574.out = true := by decide +kernel

def cell1574 : CellCertificate where
  tauBall := tau1574
  contactCenter := center1574
  contactBall := contact1574
  work := work1574
  center_sq := center_sq1574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1574.1
  jac_ok := checks1574.2.1
  accepted := checks1574.2.2

def tau1575 : RatBall :=
  ⟨⟨11/320, -23/64⟩, 3/640⟩
def center1575 : GaussianRat :=
  ⟨27492413/1000000000, -2037657/7812500⟩
def contact1575 : RatBall := localContactBall tau1575 center1575
def work1575 : RoundedTauEval :=
  evalTau precision tau1575 contact1575 logTwoBall

theorem center_sq1575 : (center1575.re : ℝ)^2 +
    (center1575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1575 : work1575.theta.ok = true ∧
    work1575.jac.invOK = true ∧ acceptsUnitSq work1575.out = true := by decide +kernel

def cell1575 : CellCertificate where
  tauBall := tau1575
  contactCenter := center1575
  contactBall := contact1575
  work := work1575
  center_sq := center_sq1575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1575.1
  jac_ok := checks1575.2.1
  accepted := checks1575.2.2

def cells : List CellCertificate := [cell1568, cell1569, cell1570, cell1571, cell1572, cell1573, cell1574, cell1575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196


