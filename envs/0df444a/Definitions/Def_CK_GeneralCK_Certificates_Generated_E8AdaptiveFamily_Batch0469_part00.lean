-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:08:18.703492+00:00
-- url     : https://prove2.me/theorems/cab0e056-7905-4bdc-8b7b-06e4ae51f0de
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0469 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3752 : RatBall :=
  ⟨⟨71/640, 241/640⟩, 3/1280⟩
def center3752 : GaussianRat :=
  ⟨89415553/1000000000, 270605413/1000000000⟩
def contact3752 : RatBall := localContactBall tau3752 center3752
def work3752 : RoundedTauEval :=
  evalTau precision tau3752 contact3752 logTwoBall

theorem center_sq3752 : (center3752.re : ℝ)^2 +
    (center3752.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3752]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3752 : work3752.theta.ok = true ∧
    work3752.jac.invOK = true ∧ acceptsUnitSq work3752.out = true := by decide +kernel

def cell3752 : CellCertificate where
  tauBall := tau3752
  contactCenter := center3752
  contactBall := contact3752
  work := work3752
  center_sq := center_sq3752
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3752.1
  jac_ok := checks3752.2.1
  accepted := checks3752.2.2

def tau3753 : RatBall :=
  ⟨⟨69/640, 243/640⟩, 3/1280⟩
def center3753 : GaussianRat :=
  ⟨87178851/1000000000, 273334167/1000000000⟩
def contact3753 : RatBall := localContactBall tau3753 center3753
def work3753 : RoundedTauEval :=
  evalTau precision tau3753 contact3753 logTwoBall

theorem center_sq3753 : (center3753.re : ℝ)^2 +
    (center3753.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3753]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3753 : work3753.theta.ok = true ∧
    work3753.jac.invOK = true ∧ acceptsUnitSq work3753.out = true := by decide +kernel

def cell3753 : CellCertificate where
  tauBall := tau3753
  contactCenter := center3753
  contactBall := contact3753
  work := work3753
  center_sq := center_sq3753
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3753.1
  jac_ok := checks3753.2.1
  accepted := checks3753.2.2

def tau3754 : RatBall :=
  ⟨⟨71/640, 243/640⟩, 3/1280⟩
def center3754 : GaussianRat :=
  ⟨89664833/1000000000, 68271613/250000000⟩
def contact3754 : RatBall := localContactBall tau3754 center3754
def work3754 : RoundedTauEval :=
  evalTau precision tau3754 contact3754 logTwoBall

theorem center_sq3754 : (center3754.re : ℝ)^2 +
    (center3754.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3754]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3754 : work3754.theta.ok = true ∧
    work3754.jac.invOK = true ∧ acceptsUnitSq work3754.out = true := by decide +kernel

def cell3754 : CellCertificate where
  tauBall := tau3754
  contactCenter := center3754
  contactBall := contact3754
  work := work3754
  center_sq := center_sq3754
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3754.1
  jac_ok := checks3754.2.1
  accepted := checks3754.2.2

def tau3755 : RatBall :=
  ⟨⟨13/128, 49/128⟩, 3/1280⟩
def center3755 : GaussianRat :=
  ⟨41214889/500000000, 1726921/6250000⟩
def contact3755 : RatBall := localContactBall tau3755 center3755
def work3755 : RoundedTauEval :=
  evalTau precision tau3755 contact3755 logTwoBall

theorem center_sq3755 : (center3755.re : ℝ)^2 +
    (center3755.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3755]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3755 : work3755.theta.ok = true ∧
    work3755.jac.invOK = true ∧ acceptsUnitSq work3755.out = true := by decide +kernel

def cell3755 : CellCertificate where
  tauBall := tau3755
  contactCenter := center3755
  contactBall := contact3755
  work := work3755
  center_sq := center_sq3755
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3755.1
  jac_ok := checks3755.2.1
  accepted := checks3755.2.2

def tau3756 : RatBall :=
  ⟨⟨67/640, 49/128⟩, 3/1280⟩
def center3756 : GaussianRat :=
  ⟨42464509/500000000, 34508699/125000000⟩
def contact3756 : RatBall := localContactBall tau3756 center3756
def work3756 : RoundedTauEval :=
  evalTau precision tau3756 contact3756 logTwoBall

theorem center_sq3756 : (center3756.re : ℝ)^2 +
    (center3756.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3756]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3756 : work3756.theta.ok = true ∧
    work3756.jac.invOK = true ∧ acceptsUnitSq work3756.out = true := by decide +kernel

def cell3756 : CellCertificate where
  tauBall := tau3756
  contactCenter := center3756
  contactBall := contact3756
  work := work3756
  center_sq := center_sq3756
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3756.1
  jac_ok := checks3756.2.1
  accepted := checks3756.2.2

def tau3757 : RatBall :=
  ⟨⟨13/128, 247/640⟩, 3/1280⟩
def center3757 : GaussianRat :=
  ⟨82665793/1000000000, 278811601/1000000000⟩
def contact3757 : RatBall := localContactBall tau3757 center3757
def work3757 : RoundedTauEval :=
  evalTau precision tau3757 contact3757 logTwoBall

theorem center_sq3757 : (center3757.re : ℝ)^2 +
    (center3757.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3757]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3757 : work3757.theta.ok = true ∧
    work3757.jac.invOK = true ∧ acceptsUnitSq work3757.out = true := by decide +kernel

def cell3757 : CellCertificate where
  tauBall := tau3757
  contactCenter := center3757
  contactBall := contact3757
  work := work3757
  center_sq := center_sq3757
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3757.1
  jac_ok := checks3757.2.1
  accepted := checks3757.2.2

def tau3758 : RatBall :=
  ⟨⟨67/640, 247/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469


