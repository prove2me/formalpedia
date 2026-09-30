-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:20:26.690108+00:00
-- url     : https://prove2.me/theorems/f4e33618-c59c-4c96-82c8-5860a99c7270
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0130 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0130_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1044 : RatBall :=
  ⟨⟨49/160, 27/160⟩, 3/320⟩
def center1044 : GaussianRat :=
  ⟨211098659/1000000000, 10718597/100000000⟩
def contact1044 : RatBall := localContactBall tau1044 center1044
def work1044 : RoundedTauEval :=
  evalTau precision tau1044 contact1044 logTwoBall

theorem center_sq1044 : (center1044.re : ℝ)^2 +
    (center1044.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1044]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1044 : work1044.theta.ok = true ∧
    work1044.jac.invOK = true ∧ acceptsUnitSq work1044.out = true := by decide +kernel

def cell1044 : CellCertificate where
  tauBall := tau1044
  contactCenter := center1044
  contactBall := contact1044
  work := work1044
  center_sq := center_sq1044
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1044.1
  jac_ok := checks1044.2.1
  accepted := checks1044.2.2

def tau1045 : RatBall :=
  ⟨⟨51/160, 27/160⟩, 3/320⟩
def center1045 : GaussianRat :=
  ⟨219098349/1000000000, 53182749/500000000⟩
def contact1045 : RatBall := localContactBall tau1045 center1045
def work1045 : RoundedTauEval :=
  evalTau precision tau1045 contact1045 logTwoBall

theorem center_sq1045 : (center1045.re : ℝ)^2 +
    (center1045.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1045]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1045 : work1045.theta.ok = true ∧
    work1045.jac.invOK = true ∧ acceptsUnitSq work1045.out = true := by decide +kernel

def cell1045 : CellCertificate where
  tauBall := tau1045
  contactCenter := center1045
  contactBall := contact1045
  work := work1045
  center_sq := center_sq1045
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1045.1
  jac_ok := checks1045.2.1
  accepted := checks1045.2.2

def tau1046 : RatBall :=
  ⟨⟨53/160, 5/32⟩, 3/320⟩
def center1046 : GaussianRat :=
  ⟨226215887/1000000000, 24408867/250000000⟩
def contact1046 : RatBall := localContactBall tau1046 center1046
def work1046 : RoundedTauEval :=
  evalTau precision tau1046 contact1046 logTwoBall

theorem center_sq1046 : (center1046.re : ℝ)^2 +
    (center1046.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1046]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1046 : work1046.theta.ok = true ∧
    work1046.jac.invOK = true ∧ acceptsUnitSq work1046.out = true := by decide +kernel

def cell1046 : CellCertificate where
  tauBall := tau1046
  contactCenter := center1046
  contactBall := contact1046
  work := work1046
  center_sq := center_sq1046
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1046.1
  jac_ok := checks1046.2.1
  accepted := checks1046.2.2

def tau1047 : RatBall :=
  ⟨⟨11/32, 5/32⟩, 3/320⟩
def center1047 : GaussianRat :=
  ⟨234063587/1000000000, 96845571/1000000000⟩
def contact1047 : RatBall := localContactBall tau1047 center1047
def work1047 : RoundedTauEval :=
  evalTau precision tau1047 contact1047 logTwoBall

theorem center_sq1047 : (center1047.re : ℝ)^2 +
    (center1047.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1047]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1047 : work1047.theta.ok = true ∧
    work1047.jac.invOK = true ∧ acceptsUnitSq work1047.out = true := by decide +kernel

def cell1047 : CellCertificate where
  tauBall := tau1047
  contactCenter := center1047
  contactBall := contact1047
  work := work1047
  center_sq := center_sq1047
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1047.1
  jac_ok := checks1047.2.1
  accepted := checks1047.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130


