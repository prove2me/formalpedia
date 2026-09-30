-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0382_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:03.075101+00:00
-- url     : https://prove2.me/theorems/f934708f-28ad-4bb4-be6a-08463e880003
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0382 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3056 : RatBall :=
  ⟨⟨67/640, -243/640⟩, 3/1280⟩
def center3056 : GaussianRat :=
  ⟨42344767/500000000, -273575317/1000000000⟩
def contact3056 : RatBall := localContactBall tau3056 center3056
def work3056 : RoundedTauEval :=
  evalTau precision tau3056 contact3056 logTwoBall

theorem center_sq3056 : (center3056.re : ℝ)^2 +
    (center3056.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3056]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3056 : work3056.theta.ok = true ∧
    work3056.jac.invOK = true ∧ acceptsUnitSq work3056.out = true := by decide +kernel

def cell3056 : CellCertificate where
  tauBall := tau3056
  contactCenter := center3056
  contactBall := contact3056
  work := work3056
  center_sq := center_sq3056
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3056.1
  jac_ok := checks3056.2.1
  accepted := checks3056.2.2

def tau3057 : RatBall :=
  ⟨⟨13/128, -241/640⟩, 3/1280⟩
def center3057 : GaussianRat :=
  ⟨40983659/500000000, -135659503/500000000⟩
def contact3057 : RatBall := localContactBall tau3057 center3057
def work3057 : RoundedTauEval :=
  evalTau precision tau3057 contact3057 logTwoBall

theorem center_sq3057 : (center3057.re : ℝ)^2 +
    (center3057.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3057]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3057 : work3057.theta.ok = true ∧
    work3057.jac.invOK = true ∧ acceptsUnitSq work3057.out = true := by decide +kernel

def cell3057 : CellCertificate where
  tauBall := tau3057
  contactCenter := center3057
  contactBall := contact3057
  work := work3057
  center_sq := center_sq3057
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3057.1
  jac_ok := checks3057.2.1
  accepted := checks3057.2.2

def tau3058 : RatBall :=
  ⟨⟨67/640, -241/640⟩, 3/1280⟩
def center3058 : GaussianRat :=
  ⟨84453299/1000000000, -5421753/20000000⟩
def contact3058 : RatBall := localContactBall tau3058 center3058
def work3058 : RoundedTauEval :=
  evalTau precision tau3058 contact3058 logTwoBall

theorem center_sq3058 : (center3058.re : ℝ)^2 +
    (center3058.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3058]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3058 : work3058.theta.ok = true ∧
    work3058.jac.invOK = true ∧ acceptsUnitSq work3058.out = true := by decide +kernel

def cell3058 : CellCertificate where
  tauBall := tau3058
  contactCenter := center3058
  contactBall := contact3058
  work := work3058
  center_sq := center_sq3058
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3058.1
  jac_ok := checks3058.2.1
  accepted := checks3058.2.2

def tau3059 : RatBall :=
  ⟨⟨69/640, -243/640⟩, 3/1280⟩
def center3059 : GaussianRat :=
  ⟨87178851/1000000000, -273334167/1000000000⟩
def contact3059 : RatBall := localContactBall tau3059 center3059
def work3059 : RoundedTauEval :=
  evalTau precision tau3059 contact3059 logTwoBall

theorem center_sq3059 : (center3059.re : ℝ)^2 +
    (center3059.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3059]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3059 : work3059.theta.ok = true ∧
    work3059.jac.invOK = true ∧ acceptsUnitSq work3059.out = true := by decide +kernel

def cell3059 : CellCertificate where
  tauBall := tau3059
  contactCenter := center3059
  contactBall := contact3059
  work := work3059
  center_sq := center_sq3059
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3059.1
  jac_ok := checks3059.2.1
  accepted := checks3059.2.2

def tau3060 : RatBall :=
  ⟨⟨71/640, -243/640⟩, 3/1280⟩
def center3060 : GaussianRat :=
  ⟨89664833/1000000000, -68271613/250000000⟩
def contact3060 : RatBall := localContactBall tau3060 center3060
def work3060 : RoundedTauEval :=
  evalTau precision tau3060 contact3060 logTwoBall

theorem center_sq3060 : (center3060.re : ℝ)^2 +
    (center3060.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3060]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3060 : work3060.theta.ok = true ∧
    work3060.jac.invOK = true ∧ acceptsUnitSq work3060.out = true := by decide +kernel

def cell3060 : CellCertificate where
  tauBall := tau3060
  contactCenter := center3060
  contactBall := contact3060
  work := work3060
  center_sq := center_sq3060
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3060.1
  jac_ok := checks3060.2.1
  accepted := checks3060.2.2

def tau3061 : RatBall :=
  ⟨⟨69/640, -241/640⟩, 3/1280⟩
def center3061 : GaussianRat :=
  ⟨10867009/125000000, -67712443/250000000⟩
def contact3061 : RatBall := localContactBall tau3061 center3061
def work3061 : RoundedTauEval :=
  evalTau precision tau3061 contact3061 logTwoBall

theorem center_sq3061 : (center3061.re : ℝ)^2 +
    (center3061.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3061]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3061 : work3061.theta.ok = true ∧
    work3061.jac.invOK = true ∧ acceptsUnitSq work3061.out = true := by decide +kernel

def cell3061 : CellCertificate where
  tauBall := tau3061
  contactCenter := center3061
  contactBall := contact3061
  work := work3061
  center_sq := center_sq3061
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3061.1
  jac_ok := checks3061.2.1
  accepted := checks3061.2.2

def tau3062 : RatBall :=
  ⟨⟨71/640, -241/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382


