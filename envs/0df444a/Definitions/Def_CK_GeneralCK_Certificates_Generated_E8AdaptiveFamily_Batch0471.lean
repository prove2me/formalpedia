-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0471
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0471
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:29:04.452342+00:00
-- url     : https://prove2.me/theorems/59274441-a372-408f-99cd-b164c9a7d8c7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0471.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3768 : RatBall :=
  ⟨⟨79/640, 241/640⟩, 3/1280⟩
def center3768 : GaussianRat :=
  ⟨99298877/1000000000, 134782023/500000000⟩
def contact3768 : RatBall := localContactBall tau3768 center3768
def work3768 : RoundedTauEval :=
  evalTau precision tau3768 contact3768 logTwoBall

theorem center_sq3768 : (center3768.re : ℝ)^2 +
    (center3768.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3768]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3768 : work3768.theta.ok = true ∧
    work3768.jac.invOK = true ∧ acceptsUnitSq work3768.out = true := by decide +kernel

def cell3768 : CellCertificate where
  tauBall := tau3768
  contactCenter := center3768
  contactBall := contact3768
  work := work3768
  center_sq := center_sq3768
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3768.1
  jac_ok := checks3768.2.1
  accepted := checks3768.2.2

def tau3769 : RatBall :=
  ⟨⟨77/640, 243/640⟩, 3/1280⟩
def center3769 : GaussianRat :=
  ⟨97101919/1000000000, 68076089/250000000⟩
def contact3769 : RatBall := localContactBall tau3769 center3769
def work3769 : RoundedTauEval :=
  evalTau precision tau3769 contact3769 logTwoBall

theorem center_sq3769 : (center3769.re : ℝ)^2 +
    (center3769.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3769]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3769 : work3769.theta.ok = true ∧
    work3769.jac.invOK = true ∧ acceptsUnitSq work3769.out = true := by decide +kernel

def cell3769 : CellCertificate where
  tauBall := tau3769
  contactCenter := center3769
  contactBall := contact3769
  work := work3769
  center_sq := center_sq3769
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3769.1
  jac_ok := checks3769.2.1
  accepted := checks3769.2.2

def tau3770 : RatBall :=
  ⟨⟨79/640, 243/640⟩, 3/1280⟩
def center3770 : GaussianRat :=
  ⟨24893429/250000000, 136015413/500000000⟩
def contact3770 : RatBall := localContactBall tau3770 center3770
def work3770 : RoundedTauEval :=
  evalTau precision tau3770 contact3770 logTwoBall

theorem center_sq3770 : (center3770.re : ℝ)^2 +
    (center3770.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3770]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3770 : work3770.theta.ok = true ∧
    work3770.jac.invOK = true ∧ acceptsUnitSq work3770.out = true := by decide +kernel

def cell3770 : CellCertificate where
  tauBall := tau3770
  contactCenter := center3770
  contactBall := contact3770
  work := work3770
  center_sq := center_sq3770
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3770.1
  jac_ok := checks3770.2.1
  accepted := checks3770.2.2

def tau3771 : RatBall :=
  ⟨⟨73/640, 49/128⟩, 3/1280⟩
def center3771 : GaussianRat :=
  ⟨92406637/1000000000, 275316291/1000000000⟩
def contact3771 : RatBall := localContactBall tau3771 center3771
def work3771 : RoundedTauEval :=
  evalTau precision tau3771 contact3771 logTwoBall

theorem center_sq3771 : (center3771.re : ℝ)^2 +
    (center3771.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3771]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3771 : work3771.theta.ok = true ∧
    work3771.jac.invOK = true ∧ acceptsUnitSq work3771.out = true := by decide +kernel

def cell3771 : CellCertificate where
  tauBall := tau3771
  contactCenter := center3771
  contactBall := contact3771
  work := work3771
  center_sq := center_sq3771
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3771.1
  jac_ok := checks3771.2.1
  accepted := checks3771.2.2

def tau3772 : RatBall :=
  ⟨⟨15/128, 49/128⟩, 3/1280⟩
def center3772 : GaussianRat :=
  ⟨9489219/100000000, 275052007/1000000000⟩
def contact3772 : RatBall := localContactBall tau3772 center3772
def work3772 : RoundedTauEval :=
  evalTau precision tau3772 contact3772 logTwoBall

theorem center_sq3772 : (center3772.re : ℝ)^2 +
    (center3772.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3772]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3772 : work3772.theta.ok = true ∧
    work3772.jac.invOK = true ∧ acceptsUnitSq work3772.out = true := by decide +kernel

def cell3772 : CellCertificate where
  tauBall := tau3772
  contactCenter := center3772
  contactBall := contact3772
  work := work3772
  center_sq := center_sq3772
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3772.1
  jac_ok := checks3772.2.1
  accepted := checks3772.2.2

def tau3773 : RatBall :=
  ⟨⟨77/640, 49/128⟩, 3/1280⟩
def center3773 : GaussianRat :=
  ⟨24343527/250000000, 34347651/125000000⟩
def contact3773 : RatBall := localContactBall tau3773 center3773
def work3773 : RoundedTauEval :=
  evalTau precision tau3773 contact3773 logTwoBall

theorem center_sq3773 : (center3773.re : ℝ)^2 +
    (center3773.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3773 : work3773.theta.ok = true ∧
    work3773.jac.invOK = true ∧ acceptsUnitSq work3773.out = true := by decide +kernel

def cell3773 : CellCertificate where
  tauBall := tau3773
  contactCenter := center3773
  contactBall := contact3773
  work := work3773
  center_sq := center_sq3773
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3773.1
  jac_ok := checks3773.2.1
  accepted := checks3773.2.2

def tau3774 : RatBall :=
  ⟨⟨81/640, 241/640⟩, 3/1280⟩
def center3774 : GaussianRat :=
  ⟨101760649/1000000000, 269287947/1000000000⟩
def contact3774 : RatBall := localContactBall tau3774 center3774
def work3774 : RoundedTauEval :=
  evalTau precision tau3774 contact3774 logTwoBall

theorem center_sq3774 : (center3774.re : ℝ)^2 +
    (center3774.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3774]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3774 : work3774.theta.ok = true ∧
    work3774.jac.invOK = true ∧ acceptsUnitSq work3774.out = true := by decide +kernel

def cell3774 : CellCertificate where
  tauBall := tau3774
  contactCenter := center3774
  contactBall := contact3774
  work := work3774
  center_sq := center_sq3774
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3774.1
  jac_ok := checks3774.2.1
  accepted := checks3774.2.2

def tau3775 : RatBall :=
  ⟨⟨83/640, 241/640⟩, 3/1280⟩
def center3775 : GaussianRat :=
  ⟨104218637/1000000000, 134502819/500000000⟩
def contact3775 : RatBall := localContactBall tau3775 center3775
def work3775 : RoundedTauEval :=
  evalTau precision tau3775 contact3775 logTwoBall

theorem center_sq3775 : (center3775.re : ℝ)^2 +
    (center3775.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3775]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3775 : work3775.theta.ok = true ∧
    work3775.jac.invOK = true ∧ acceptsUnitSq work3775.out = true := by decide +kernel

def cell3775 : CellCertificate where
  tauBall := tau3775
  contactCenter := center3775
  contactBall := contact3775
  work := work3775
  center_sq := center_sq3775
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3775.1
  jac_ok := checks3775.2.1
  accepted := checks3775.2.2

def cells : List CellCertificate := [cell3768, cell3769, cell3770, cell3771, cell3772, cell3773, cell3774, cell3775]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471

end


