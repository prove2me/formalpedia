-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0468_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:58:11.265511+00:00
-- url     : https://prove2.me/theorems/e3ffa346-cd14-45d6-8f65-676cf296fd36
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0468 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3744 : RatBall :=
  ⟨⟨19/128, 237/640⟩, 3/1280⟩
def center3744 : GaussianRat :=
  ⟨29562099/250000000, 262332709/1000000000⟩
def contact3744 : RatBall := localContactBall tau3744 center3744
def work3744 : RoundedTauEval :=
  evalTau precision tau3744 contact3744 logTwoBall

theorem center_sq3744 : (center3744.re : ℝ)^2 +
    (center3744.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3744]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3744 : work3744.theta.ok = true ∧
    work3744.jac.invOK = true ∧ acceptsUnitSq work3744.out = true := by decide +kernel

def cell3744 : CellCertificate where
  tauBall := tau3744
  contactCenter := center3744
  contactBall := contact3744
  work := work3744
  center_sq := center_sq3744
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3744.1
  jac_ok := checks3744.2.1
  accepted := checks3744.2.2

def tau3745 : RatBall :=
  ⟨⟨93/640, 239/640⟩, 3/1280⟩
def center3745 : GaussianRat :=
  ⟨116135629/1000000000, 265069807/1000000000⟩
def contact3745 : RatBall := localContactBall tau3745 center3745
def work3745 : RoundedTauEval :=
  evalTau precision tau3745 contact3745 logTwoBall

theorem center_sq3745 : (center3745.re : ℝ)^2 +
    (center3745.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3745]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3745 : work3745.theta.ok = true ∧
    work3745.jac.invOK = true ∧ acceptsUnitSq work3745.out = true := by decide +kernel

def cell3745 : CellCertificate where
  tauBall := tau3745
  contactCenter := center3745
  contactBall := contact3745
  work := work3745
  center_sq := center_sq3745
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3745.1
  jac_ok := checks3745.2.1
  accepted := checks3745.2.2

def tau3746 : RatBall :=
  ⟨⟨19/128, 239/640⟩, 3/1280⟩
def center3746 : GaussianRat :=
  ⟨118563451/1000000000, 66188883/250000000⟩
def contact3746 : RatBall := localContactBall tau3746 center3746
def work3746 : RoundedTauEval :=
  evalTau precision tau3746 contact3746 logTwoBall

theorem center_sq3746 : (center3746.re : ℝ)^2 +
    (center3746.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3746]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3746 : work3746.theta.ok = true ∧
    work3746.jac.invOK = true ∧ acceptsUnitSq work3746.out = true := by decide +kernel

def cell3746 : CellCertificate where
  tauBall := tau3746
  contactCenter := center3746
  contactBall := contact3746
  work := work3746
  center_sq := center_sq3746
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3746.1
  jac_ok := checks3746.2.1
  accepted := checks3746.2.2

def tau3747 : RatBall :=
  ⟨⟨13/128, 241/640⟩, 3/1280⟩
def center3747 : GaussianRat :=
  ⟨40983659/500000000, 135659503/500000000⟩
def contact3747 : RatBall := localContactBall tau3747 center3747
def work3747 : RoundedTauEval :=
  evalTau precision tau3747 contact3747 logTwoBall

theorem center_sq3747 : (center3747.re : ℝ)^2 +
    (center3747.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3747]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3747 : work3747.theta.ok = true ∧
    work3747.jac.invOK = true ∧ acceptsUnitSq work3747.out = true := by decide +kernel

def cell3747 : CellCertificate where
  tauBall := tau3747
  contactCenter := center3747
  contactBall := contact3747
  work := work3747
  center_sq := center_sq3747
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3747.1
  jac_ok := checks3747.2.1
  accepted := checks3747.2.2

def tau3748 : RatBall :=
  ⟨⟨67/640, 241/640⟩, 3/1280⟩
def center3748 : GaussianRat :=
  ⟨84453299/1000000000, 5421753/20000000⟩
def contact3748 : RatBall := localContactBall tau3748 center3748
def work3748 : RoundedTauEval :=
  evalTau precision tau3748 contact3748 logTwoBall

theorem center_sq3748 : (center3748.re : ℝ)^2 +
    (center3748.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3748]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3748 : work3748.theta.ok = true ∧
    work3748.jac.invOK = true ∧ acceptsUnitSq work3748.out = true := by decide +kernel

def cell3748 : CellCertificate where
  tauBall := tau3748
  contactCenter := center3748
  contactBall := contact3748
  work := work3748
  center_sq := center_sq3748
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3748.1
  jac_ok := checks3748.2.1
  accepted := checks3748.2.2

def tau3749 : RatBall :=
  ⟨⟨13/128, 243/640⟩, 3/1280⟩
def center3749 : GaussianRat :=
  ⟨82196967/1000000000, 136904929/500000000⟩
def contact3749 : RatBall := localContactBall tau3749 center3749
def work3749 : RoundedTauEval :=
  evalTau precision tau3749 contact3749 logTwoBall

theorem center_sq3749 : (center3749.re : ℝ)^2 +
    (center3749.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3749]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3749 : work3749.theta.ok = true ∧
    work3749.jac.invOK = true ∧ acceptsUnitSq work3749.out = true := by decide +kernel

def cell3749 : CellCertificate where
  tauBall := tau3749
  contactCenter := center3749
  contactBall := contact3749
  work := work3749
  center_sq := center_sq3749
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3749.1
  jac_ok := checks3749.2.1
  accepted := checks3749.2.2

def tau3750 : RatBall :=
  ⟨⟨67/640, 243/640⟩, 3/1280⟩
def center3750 : GaussianRat :=
  ⟨42344767/500000000, 273575317/1000000000⟩
def contact3750 : RatBall := localContactBall tau3750 center3750
def work3750 : RoundedTauEval :=
  evalTau precision tau3750 contact3750 logTwoBall

theorem center_sq3750 : (center3750.re : ℝ)^2 +
    (center3750.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3750]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468


