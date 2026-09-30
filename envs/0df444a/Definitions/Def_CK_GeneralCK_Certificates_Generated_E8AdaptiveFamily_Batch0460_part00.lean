-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0460_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:34:39.710632+00:00
-- url     : https://prove2.me/theorems/bace42e6-8a20-48e1-b4fd-3256170a7f39
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0460 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3680 : RatBall :=
  ⟨⟨11/128, 249/640⟩, 3/1280⟩
def center3680 : GaussianRat :=
  ⟨70293283/1000000000, 14121991/50000000⟩
def contact3680 : RatBall := localContactBall tau3680 center3680
def work3680 : RoundedTauEval :=
  evalTau precision tau3680 contact3680 logTwoBall

theorem center_sq3680 : (center3680.re : ℝ)^2 +
    (center3680.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3680]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3680 : work3680.theta.ok = true ∧
    work3680.jac.invOK = true ∧ acceptsUnitSq work3680.out = true := by decide +kernel

def cell3680 : CellCertificate where
  tauBall := tau3680
  contactCenter := center3680
  contactBall := contact3680
  work := work3680
  center_sq := center_sq3680
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3680.1
  jac_ok := checks3680.2.1
  accepted := checks3680.2.2

def tau3681 : RatBall :=
  ⟨⟨53/640, 251/640⟩, 3/1280⟩
def center3681 : GaussianRat :=
  ⟨67962093/1000000000, 285178227/1000000000⟩
def contact3681 : RatBall := localContactBall tau3681 center3681
def work3681 : RoundedTauEval :=
  evalTau precision tau3681 contact3681 logTwoBall

theorem center_sq3681 : (center3681.re : ℝ)^2 +
    (center3681.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3681]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3681 : work3681.theta.ok = true ∧
    work3681.jac.invOK = true ∧ acceptsUnitSq work3681.out = true := by decide +kernel

def cell3681 : CellCertificate where
  tauBall := tau3681
  contactCenter := center3681
  contactBall := contact3681
  work := work3681
  center_sq := center_sq3681
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3681.1
  jac_ok := checks3681.2.1
  accepted := checks3681.2.2

def tau3682 : RatBall :=
  ⟨⟨11/128, 251/640⟩, 3/1280⟩
def center3682 : GaussianRat :=
  ⟨70500491/1000000000, 35621651/125000000⟩
def contact3682 : RatBall := localContactBall tau3682 center3682
def work3682 : RoundedTauEval :=
  evalTau precision tau3682 contact3682 logTwoBall

theorem center_sq3682 : (center3682.re : ℝ)^2 +
    (center3682.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3682]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3682 : work3682.theta.ok = true ∧
    work3682.jac.invOK = true ∧ acceptsUnitSq work3682.out = true := by decide +kernel

def cell3682 : CellCertificate where
  tauBall := tau3682
  contactCenter := center3682
  contactBall := contact3682
  work := work3682
  center_sq := center_sq3682
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3682.1
  jac_ok := checks3682.2.1
  accepted := checks3682.2.2

def tau3683 : RatBall :=
  ⟨⟨57/640, 249/640⟩, 3/1280⟩
def center3683 : GaussianRat :=
  ⟨14564333/200000000, 70557619/250000000⟩
def contact3683 : RatBall := localContactBall tau3683 center3683
def work3683 : RoundedTauEval :=
  evalTau precision tau3683 contact3683 logTwoBall

theorem center_sq3683 : (center3683.re : ℝ)^2 +
    (center3683.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3683]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3683 : work3683.theta.ok = true ∧
    work3683.jac.invOK = true ∧ acceptsUnitSq work3683.out = true := by decide +kernel

def cell3683 : CellCertificate where
  tauBall := tau3683
  contactCenter := center3683
  contactBall := contact3683
  work := work3683
  center_sq := center_sq3683
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3683.1
  jac_ok := checks3683.2.1
  accepted := checks3683.2.2

def tau3684 : RatBall :=
  ⟨⟨59/640, 249/640⟩, 3/1280⟩
def center3684 : GaussianRat :=
  ⟨75347127/1000000000, 8812939/31250000⟩
def contact3684 : RatBall := localContactBall tau3684 center3684
def work3684 : RoundedTauEval :=
  evalTau precision tau3684 contact3684 logTwoBall

theorem center_sq3684 : (center3684.re : ℝ)^2 +
    (center3684.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3684]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3684 : work3684.theta.ok = true ∧
    work3684.jac.invOK = true ∧ acceptsUnitSq work3684.out = true := by decide +kernel

def cell3684 : CellCertificate where
  tauBall := tau3684
  contactCenter := center3684
  contactBall := contact3684
  work := work3684
  center_sq := center_sq3684
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3684.1
  jac_ok := checks3684.2.1
  accepted := checks3684.2.2

def tau3685 : RatBall :=
  ⟨⟨61/640, 249/640⟩, 3/1280⟩
def center3685 : GaussianRat :=
  ⟨38934787/500000000, 281790577/1000000000⟩
def contact3685 : RatBall := localContactBall tau3685 center3685
def work3685 : RoundedTauEval :=
  evalTau precision tau3685 contact3685 logTwoBall

theorem center_sq3685 : (center3685.re : ℝ)^2 +
    (center3685.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3685]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3685 : work3685.theta.ok = true ∧
    work3685.jac.invOK = true ∧ acceptsUnitSq work3685.out = true := by decide +kernel

def cell3685 : CellCertificate where
  tauBall := tau3685
  contactCenter := center3685
  contactBall := contact3685
  work := work3685
  center_sq := center_sq3685
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3685.1
  jac_ok := checks3685.2.1
  accepted := checks3685.2.2

def tau3686 : RatBall :=
  ⟨⟨63/640, 249/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460


