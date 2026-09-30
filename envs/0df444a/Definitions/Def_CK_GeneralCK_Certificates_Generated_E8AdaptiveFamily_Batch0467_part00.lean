-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0467_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:17:48.998704+00:00
-- url     : https://prove2.me/theorems/249abd07-d0fb-4645-85f1-fdc84a8e625a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0467 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3736 : RatBall :=
  ⟨⟨19/128, 233/640⟩, 3/1280⟩
def center3736 : GaussianRat :=
  ⟨7351929/62500000, 128752067/500000000⟩
def contact3736 : RatBall := localContactBall tau3736 center3736
def work3736 : RoundedTauEval :=
  evalTau precision tau3736 contact3736 logTwoBall

theorem center_sq3736 : (center3736.re : ℝ)^2 +
    (center3736.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3736]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3736 : work3736.theta.ok = true ∧
    work3736.jac.invOK = true ∧ acceptsUnitSq work3736.out = true := by decide +kernel

def cell3736 : CellCertificate where
  tauBall := tau3736
  contactCenter := center3736
  contactBall := contact3736
  work := work3736
  center_sq := center_sq3736
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3736.1
  jac_ok := checks3736.2.1
  accepted := checks3736.2.2

def tau3737 : RatBall :=
  ⟨⟨93/640, 47/128⟩, 3/1280⟩
def center3737 : GaussianRat :=
  ⟨115521207/1000000000, 32527691/125000000⟩
def contact3737 : RatBall := localContactBall tau3737 center3737
def work3737 : RoundedTauEval :=
  evalTau precision tau3737 contact3737 logTwoBall

theorem center_sq3737 : (center3737.re : ℝ)^2 +
    (center3737.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3737]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3737 : work3737.theta.ok = true ∧
    work3737.jac.invOK = true ∧ acceptsUnitSq work3737.out = true := by decide +kernel

def cell3737 : CellCertificate where
  tauBall := tau3737
  contactCenter := center3737
  contactBall := contact3737
  work := work3737
  center_sq := center_sq3737
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3737.1
  jac_ok := checks3737.2.1
  accepted := checks3737.2.2

def tau3738 : RatBall :=
  ⟨⟨19/128, 47/128⟩, 3/1280⟩
def center3738 : GaussianRat :=
  ⟨117937551/1000000000, 649789/2500000⟩
def contact3738 : RatBall := localContactBall tau3738 center3738
def work3738 : RoundedTauEval :=
  evalTau precision tau3738 contact3738 logTwoBall

theorem center_sq3738 : (center3738.re : ℝ)^2 +
    (center3738.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3738]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3738 : work3738.theta.ok = true ∧
    work3738.jac.invOK = true ∧ acceptsUnitSq work3738.out = true := by decide +kernel

def cell3738 : CellCertificate where
  tauBall := tau3738
  contactCenter := center3738
  contactBall := contact3738
  work := work3738
  center_sq := center_sq3738
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3738.1
  jac_ok := checks3738.2.1
  accepted := checks3738.2.2

def tau3739 : RatBall :=
  ⟨⟨89/640, 237/640⟩, 3/1280⟩
def center3739 : GaussianRat :=
  ⟨55484957/500000000, 65811399/250000000⟩
def contact3739 : RatBall := localContactBall tau3739 center3739
def work3739 : RoundedTauEval :=
  evalTau precision tau3739 contact3739 logTwoBall

theorem center_sq3739 : (center3739.re : ℝ)^2 +
    (center3739.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3739]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3739 : work3739.theta.ok = true ∧
    work3739.jac.invOK = true ∧ acceptsUnitSq work3739.out = true := by decide +kernel

def cell3739 : CellCertificate where
  tauBall := tau3739
  contactCenter := center3739
  contactBall := contact3739
  work := work3739
  center_sq := center_sq3739
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3739.1
  jac_ok := checks3739.2.1
  accepted := checks3739.2.2

def tau3740 : RatBall :=
  ⟨⟨91/640, 237/640⟩, 3/1280⟩
def center3740 : GaussianRat :=
  ⟨22680033/200000000, 131473549/500000000⟩
def contact3740 : RatBall := localContactBall tau3740 center3740
def work3740 : RoundedTauEval :=
  evalTau precision tau3740 contact3740 logTwoBall

theorem center_sq3740 : (center3740.re : ℝ)^2 +
    (center3740.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3740]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3740 : work3740.theta.ok = true ∧
    work3740.jac.invOK = true ∧ acceptsUnitSq work3740.out = true := by decide +kernel

def cell3740 : CellCertificate where
  tauBall := tau3740
  contactCenter := center3740
  contactBall := contact3740
  work := work3740
  center_sq := center_sq3740
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3740.1
  jac_ok := checks3740.2.1
  accepted := checks3740.2.2

def tau3741 : RatBall :=
  ⟨⟨89/640, 239/640⟩, 3/1280⟩
def center3741 : GaussianRat :=
  ⟨111267493/1000000000, 265680799/1000000000⟩
def contact3741 : RatBall := localContactBall tau3741 center3741
def work3741 : RoundedTauEval :=
  evalTau precision tau3741 contact3741 logTwoBall

theorem center_sq3741 : (center3741.re : ℝ)^2 +
    (center3741.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3741]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3741 : work3741.theta.ok = true ∧
    work3741.jac.invOK = true ∧ acceptsUnitSq work3741.out = true := by decide +kernel

def cell3741 : CellCertificate where
  tauBall := tau3741
  contactCenter := center3741
  contactBall := contact3741
  work := work3741
  center_sq := center_sq3741
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3741.1
  jac_ok := checks3741.2.1
  accepted := checks3741.2.2

def tau3742 : RatBall :=
  ⟨⟨91/640, 239/640⟩, 3/1280⟩
def center3742 : GaussianRat :=
  ⟨113703619/1000000000, 265378247/1000000000⟩
def contact3742 : RatBall := localContactBall tau3742 center3742
def work3742 : RoundedTauEval :=
  evalTau precision tau3742 contact3742 logTwoBall

theorem center_sq3742 : (center3742.re : ℝ)^2 +
    (center3742.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3742]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467


