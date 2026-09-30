-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:34:18.70812+00:00
-- url     : https://prove2.me/theorems/2ed144c3-65ff-48ee-9b5a-7809777507cf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0125 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0125_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1003 : work1003.theta.ok = true ∧
    work1003.jac.invOK = true ∧ acceptsUnitSq work1003.out = true := by decide +kernel

def cell1003 : CellCertificate where
  tauBall := tau1003
  contactCenter := center1003
  contactBall := contact1003
  work := work1003
  center_sq := center_sq1003
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1003.1
  jac_ok := checks1003.2.1
  accepted := checks1003.2.2

def tau1004 : RatBall :=
  ⟨⟨37/160, 31/160⟩, 3/320⟩
def center1004 : GaussianRat :=
  ⟨163226979/1000000000, 128476919/1000000000⟩
def contact1004 : RatBall := localContactBall tau1004 center1004
def work1004 : RoundedTauEval :=
  evalTau precision tau1004 contact1004 logTwoBall

theorem center_sq1004 : (center1004.re : ℝ)^2 +
    (center1004.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1004]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1004 : work1004.theta.ok = true ∧
    work1004.jac.invOK = true ∧ acceptsUnitSq work1004.out = true := by decide +kernel

def cell1004 : CellCertificate where
  tauBall := tau1004
  contactCenter := center1004
  contactBall := contact1004
  work := work1004
  center_sq := center_sq1004
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1004.1
  jac_ok := checks1004.2.1
  accepted := checks1004.2.2

def tau1005 : RatBall :=
  ⟨⟨39/160, 31/160⟩, 3/320⟩
def center1005 : GaussianRat :=
  ⟨10728219/62500000, 127685733/1000000000⟩
def contact1005 : RatBall := localContactBall tau1005 center1005
def work1005 : RoundedTauEval :=
  evalTau precision tau1005 contact1005 logTwoBall

theorem center_sq1005 : (center1005.re : ℝ)^2 +
    (center1005.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1005]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1005 : work1005.theta.ok = true ∧
    work1005.jac.invOK = true ∧ acceptsUnitSq work1005.out = true := by decide +kernel

def cell1005 : CellCertificate where
  tauBall := tau1005
  contactCenter := center1005
  contactBall := contact1005
  work := work1005
  center_sq := center_sq1005
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1005.1
  jac_ok := checks1005.2.1
  accepted := checks1005.2.2

def tau1006 : RatBall :=
  ⟨⟨9/32, 5/32⟩, 3/320⟩
def center1006 : GaussianRat :=
  ⟨194169161/1000000000, 100614871/1000000000⟩
def contact1006 : RatBall := localContactBall tau1006 center1006
def work1006 : RoundedTauEval :=
  evalTau precision tau1006 contact1006 logTwoBall

theorem center_sq1006 : (center1006.re : ℝ)^2 +
    (center1006.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1006]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1006 : work1006.theta.ok = true ∧
    work1006.jac.invOK = true ∧ acceptsUnitSq work1006.out = true := by decide +kernel

def cell1006 : CellCertificate where
  tauBall := tau1006
  contactCenter := center1006
  contactBall := contact1006
  work := work1006
  center_sq := center_sq1006
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1006.1
  jac_ok := checks1006.2.1
  accepted := checks1006.2.2

def tau1007 : RatBall :=
  ⟨⟨47/160, 5/32⟩, 3/320⟩
def center1007 : GaussianRat :=
  ⟨202276259/1000000000, 49949641/500000000⟩
def contact1007 : RatBall := localContactBall tau1007 center1007

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125


