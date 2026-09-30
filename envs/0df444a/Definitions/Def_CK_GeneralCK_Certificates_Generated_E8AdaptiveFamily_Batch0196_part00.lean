-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0196_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0196_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:19:36.033815+00:00
-- url     : https://prove2.me/theorems/0d755eb0-8bcc-491b-a8ce-8ac1e549a3ed
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0196 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1568 : RatBall :=
  ⟨⟨9/320, -117/320⟩, 3/640⟩
def center1568 : GaussianRat :=
  ⟨4524341/200000000, -53192453/200000000⟩
def contact1568 : RatBall := localContactBall tau1568 center1568
def work1568 : RoundedTauEval :=
  evalTau precision tau1568 contact1568 logTwoBall

theorem center_sq1568 : (center1568.re : ℝ)^2 +
    (center1568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1568 : work1568.theta.ok = true ∧
    work1568.jac.invOK = true ∧ acceptsUnitSq work1568.out = true := by decide +kernel

def cell1568 : CellCertificate where
  tauBall := tau1568
  contactCenter := center1568
  contactBall := contact1568
  work := work1568
  center_sq := center_sq1568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1568.1
  jac_ok := checks1568.2.1
  accepted := checks1568.2.2

def tau1569 : RatBall :=
  ⟨⟨11/320, -117/320⟩, 3/640⟩
def center1569 : GaussianRat :=
  ⟨863803/31250000, -33228071/125000000⟩
def contact1569 : RatBall := localContactBall tau1569 center1569
def work1569 : RoundedTauEval :=
  evalTau precision tau1569 contact1569 logTwoBall

theorem center_sq1569 : (center1569.re : ℝ)^2 +
    (center1569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1569 : work1569.theta.ok = true ∧
    work1569.jac.invOK = true ∧ acceptsUnitSq work1569.out = true := by decide +kernel

def cell1569 : CellCertificate where
  tauBall := tau1569
  contactCenter := center1569
  contactBall := contact1569
  work := work1569
  center_sq := center_sq1569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1569.1
  jac_ok := checks1569.2.1
  accepted := checks1569.2.2

def tau1570 : RatBall :=
  ⟨⟨13/320, -119/320⟩, 3/640⟩
def center1570 : GaussianRat :=
  ⟨32838611/1000000000, -135343343/500000000⟩
def contact1570 : RatBall := localContactBall tau1570 center1570
def work1570 : RoundedTauEval :=
  evalTau precision tau1570 contact1570 logTwoBall

theorem center_sq1570 : (center1570.re : ℝ)^2 +
    (center1570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1570 : work1570.theta.ok = true ∧
    work1570.jac.invOK = true ∧ acceptsUnitSq work1570.out = true := by decide +kernel

def cell1570 : CellCertificate where
  tauBall := tau1570
  contactCenter := center1570
  contactBall := contact1570
  work := work1570
  center_sq := center_sq1570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1570.1
  jac_ok := checks1570.2.1
  accepted := checks1570.2.2

def tau1571 : RatBall :=
  ⟨⟨3/64, -119/320⟩, 3/640⟩
def center1571 : GaussianRat :=
  ⟨18938457/500000000, -5409781/20000000⟩
def contact1571 : RatBall := localContactBall tau1571 center1571
def work1571 : RoundedTauEval :=
  evalTau precision tau1571 contact1571 logTwoBall

theorem center_sq1571 : (center1571.re : ℝ)^2 +
    (center1571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1571 : work1571.theta.ok = true ∧
    work1571.jac.invOK = true ∧ acceptsUnitSq work1571.out = true := by decide +kernel

def cell1571 : CellCertificate where
  tauBall := tau1571
  contactCenter := center1571
  contactBall := contact1571
  work := work1571
  center_sq := center_sq1571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1571.1
  jac_ok := checks1571.2.1
  accepted := checks1571.2.2

def tau1572 : RatBall :=
  ⟨⟨13/320, -117/320⟩, 3/640⟩
def center1572 : GaussianRat :=
  ⟨6531493/200000000, -265659553/1000000000⟩
def contact1572 : RatBall := localContactBall tau1572 center1572
def work1572 : RoundedTauEval :=
  evalTau precision tau1572 contact1572 logTwoBall

theorem center_sq1572 : (center1572.re : ℝ)^2 +
    (center1572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1572 : work1572.theta.ok = true ∧
    work1572.jac.invOK = true ∧ acceptsUnitSq work1572.out = true := by decide +kernel

def cell1572 : CellCertificate where
  tauBall := tau1572
  contactCenter := center1572
  contactBall := contact1572
  work := work1572
  center_sq := center_sq1572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1572.1
  jac_ok := checks1572.2.1
  accepted := checks1572.2.2

def tau1573 : RatBall :=
  ⟨⟨3/64, -117/320⟩, 3/640⟩
def center1573 : GaussianRat :=
  ⟨18834129/500000000, -13273367/50000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196


