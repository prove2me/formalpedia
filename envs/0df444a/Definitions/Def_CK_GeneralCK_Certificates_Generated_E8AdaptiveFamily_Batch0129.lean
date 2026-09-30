-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0129
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0129
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:26:20.735247+00:00
-- url     : https://prove2.me/theorems/d9391d06-97ff-4c80-a483-5d4d5afec342
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0129.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1032 : RatBall :=
  ⟨⟨57/160, 19/160⟩, 3/320⟩
def center1032 : GaussianRat :=
  ⟨239711471/1000000000, 72866371/1000000000⟩
def contact1032 : RatBall := localContactBall tau1032 center1032
def work1032 : RoundedTauEval :=
  evalTau precision tau1032 contact1032 logTwoBall

theorem center_sq1032 : (center1032.re : ℝ)^2 +
    (center1032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1032 : work1032.theta.ok = true ∧
    work1032.jac.invOK = true ∧ acceptsUnitSq work1032.out = true := by decide +kernel

def cell1032 : CellCertificate where
  tauBall := tau1032
  contactCenter := center1032
  contactBall := contact1032
  work := work1032
  center_sq := center_sq1032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1032.1
  jac_ok := checks1032.2.1
  accepted := checks1032.2.2

def tau1033 : RatBall :=
  ⟨⟨59/160, 19/160⟩, 3/320⟩
def center1033 : GaussianRat :=
  ⟨247383851/1000000000, 72251673/1000000000⟩
def contact1033 : RatBall := localContactBall tau1033 center1033
def work1033 : RoundedTauEval :=
  evalTau precision tau1033 contact1033 logTwoBall

theorem center_sq1033 : (center1033.re : ℝ)^2 +
    (center1033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1033 : work1033.theta.ok = true ∧
    work1033.jac.invOK = true ∧ acceptsUnitSq work1033.out = true := by decide +kernel

def cell1033 : CellCertificate where
  tauBall := tau1033
  contactCenter := center1033
  contactBall := contact1033
  work := work1033
  center_sq := center_sq1033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1033.1
  jac_ok := checks1033.2.1
  accepted := checks1033.2.2

def tau1034 : RatBall :=
  ⟨⟨61/160, 17/160⟩, 3/320⟩
def center1034 : GaussianRat :=
  ⟨254392641/1000000000, 20019/312500⟩
def contact1034 : RatBall := localContactBall tau1034 center1034
def work1034 : RoundedTauEval :=
  evalTau precision tau1034 contact1034 logTwoBall

theorem center_sq1034 : (center1034.re : ℝ)^2 +
    (center1034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1034 : work1034.theta.ok = true ∧
    work1034.jac.invOK = true ∧ acceptsUnitSq work1034.out = true := by decide +kernel

def cell1034 : CellCertificate where
  tauBall := tau1034
  contactCenter := center1034
  contactBall := contact1034
  work := work1034
  center_sq := center_sq1034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1034.1
  jac_ok := checks1034.2.1
  accepted := checks1034.2.2

def tau1035 : RatBall :=
  ⟨⟨61/160, 19/160⟩, 3/320⟩
def center1035 : GaussianRat :=
  ⟨31873559/125000000, 7162653/100000000⟩
def contact1035 : RatBall := localContactBall tau1035 center1035
def work1035 : RoundedTauEval :=
  evalTau precision tau1035 contact1035 logTwoBall

theorem center_sq1035 : (center1035.re : ℝ)^2 +
    (center1035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1035 : work1035.theta.ok = true ∧
    work1035.jac.invOK = true ∧ acceptsUnitSq work1035.out = true := by decide +kernel

def cell1035 : CellCertificate where
  tauBall := tau1035
  contactCenter := center1035
  contactBall := contact1035
  work := work1035
  center_sq := center_sq1035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1035.1
  jac_ok := checks1035.2.1
  accepted := checks1035.2.2

def tau1036 : RatBall :=
  ⟨⟨57/160, 21/160⟩, 3/320⟩
def center1036 : GaussianRat :=
  ⟨120177071/500000000, 16115617/200000000⟩
def contact1036 : RatBall := localContactBall tau1036 center1036
def work1036 : RoundedTauEval :=
  evalTau precision tau1036 contact1036 logTwoBall

theorem center_sq1036 : (center1036.re : ℝ)^2 +
    (center1036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1036 : work1036.theta.ok = true ∧
    work1036.jac.invOK = true ∧ acceptsUnitSq work1036.out = true := by decide +kernel

def cell1036 : CellCertificate where
  tauBall := tau1036
  contactCenter := center1036
  contactBall := contact1036
  work := work1036
  center_sq := center_sq1036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1036.1
  jac_ok := checks1036.2.1
  accepted := checks1036.2.2

def tau1037 : RatBall :=
  ⟨⟨59/160, 21/160⟩, 3/320⟩
def center1037 : GaussianRat :=
  ⟨124018963/500000000, 79895753/1000000000⟩
def contact1037 : RatBall := localContactBall tau1037 center1037
def work1037 : RoundedTauEval :=
  evalTau precision tau1037 contact1037 logTwoBall

theorem center_sq1037 : (center1037.re : ℝ)^2 +
    (center1037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1037 : work1037.theta.ok = true ∧
    work1037.jac.invOK = true ∧ acceptsUnitSq work1037.out = true := by decide +kernel

def cell1037 : CellCertificate where
  tauBall := tau1037
  contactCenter := center1037
  contactBall := contact1037
  work := work1037
  center_sq := center_sq1037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1037.1
  jac_ok := checks1037.2.1
  accepted := checks1037.2.2

def tau1038 : RatBall :=
  ⟨⟨57/160, 23/160⟩, 3/320⟩
def center1038 : GaussianRat :=
  ⟨30133041/125000000, 17660441/200000000⟩
def contact1038 : RatBall := localContactBall tau1038 center1038
def work1038 : RoundedTauEval :=
  evalTau precision tau1038 contact1038 logTwoBall

theorem center_sq1038 : (center1038.re : ℝ)^2 +
    (center1038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1038 : work1038.theta.ok = true ∧
    work1038.jac.invOK = true ∧ acceptsUnitSq work1038.out = true := by decide +kernel

def cell1038 : CellCertificate where
  tauBall := tau1038
  contactCenter := center1038
  contactBall := contact1038
  work := work1038
  center_sq := center_sq1038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1038.1
  jac_ok := checks1038.2.1
  accepted := checks1038.2.2

def tau1039 : RatBall :=
  ⟨⟨59/160, 23/160⟩, 3/320⟩
def center1039 : GaussianRat :=
  ⟨248760621/1000000000, 43775671/500000000⟩
def contact1039 : RatBall := localContactBall tau1039 center1039
def work1039 : RoundedTauEval :=
  evalTau precision tau1039 contact1039 logTwoBall

theorem center_sq1039 : (center1039.re : ℝ)^2 +
    (center1039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1039 : work1039.theta.ok = true ∧
    work1039.jac.invOK = true ∧ acceptsUnitSq work1039.out = true := by decide +kernel

def cell1039 : CellCertificate where
  tauBall := tau1039
  contactCenter := center1039
  contactBall := contact1039
  work := work1039
  center_sq := center_sq1039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1039.1
  jac_ok := checks1039.2.1
  accepted := checks1039.2.2

def cells : List CellCertificate := [cell1032, cell1033, cell1034, cell1035, cell1036, cell1037, cell1038, cell1039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129

end


