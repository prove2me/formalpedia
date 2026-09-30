-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0386_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:55.105278+00:00
-- url     : https://prove2.me/theorems/a71f7789-1c32-4462-9c51-d8e9e8aabb05
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0386 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3088 : RatBall :=
  ⟨⟨71/640, -237/640⟩, 3/1280⟩
def center3088 : GaussianRat :=
  ⟨2223177/25000000, -53132513/200000000⟩
def contact3088 : RatBall := localContactBall tau3088 center3088
def work3088 : RoundedTauEval :=
  evalTau precision tau3088 contact3088 logTwoBall

theorem center_sq3088 : (center3088.re : ℝ)^2 +
    (center3088.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3088]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3088 : work3088.theta.ok = true ∧
    work3088.jac.invOK = true ∧ acceptsUnitSq work3088.out = true := by decide +kernel

def cell3088 : CellCertificate where
  tauBall := tau3088
  contactCenter := center3088
  contactBall := contact3088
  work := work3088
  center_sq := center_sq3088
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3088.1
  jac_ok := checks3088.2.1
  accepted := checks3088.2.2

def tau3089 : RatBall :=
  ⟨⟨73/640, -239/640⟩, 3/1280⟩
def center3089 : GaussianRat :=
  ⟨91639379/1000000000, -267883413/1000000000⟩
def contact3089 : RatBall := localContactBall tau3089 center3089
def work3089 : RoundedTauEval :=
  evalTau precision tau3089 contact3089 logTwoBall

theorem center_sq3089 : (center3089.re : ℝ)^2 +
    (center3089.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3089]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3089 : work3089.theta.ok = true ∧
    work3089.jac.invOK = true ∧ acceptsUnitSq work3089.out = true := by decide +kernel

def cell3089 : CellCertificate where
  tauBall := tau3089
  contactCenter := center3089
  contactBall := contact3089
  work := work3089
  center_sq := center_sq3089
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3089.1
  jac_ok := checks3089.2.1
  accepted := checks3089.2.2

def tau3090 : RatBall :=
  ⟨⟨15/128, -239/640⟩, 3/1280⟩
def center3090 : GaussianRat :=
  ⟨23526423/250000000, -133814851/500000000⟩
def contact3090 : RatBall := localContactBall tau3090 center3090
def work3090 : RoundedTauEval :=
  evalTau precision tau3090 contact3090 logTwoBall

theorem center_sq3090 : (center3090.re : ℝ)^2 +
    (center3090.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3090]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3090 : work3090.theta.ok = true ∧
    work3090.jac.invOK = true ∧ acceptsUnitSq work3090.out = true := by decide +kernel

def cell3090 : CellCertificate where
  tauBall := tau3090
  contactCenter := center3090
  contactBall := contact3090
  work := work3090
  center_sq := center_sq3090
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3090.1
  jac_ok := checks3090.2.1
  accepted := checks3090.2.2

def tau3091 : RatBall :=
  ⟨⟨73/640, -237/640⟩, 3/1280⟩
def center3091 : GaussianRat :=
  ⟨45695259/500000000, -6635463/25000000⟩
def contact3091 : RatBall := localContactBall tau3091 center3091
def work3091 : RoundedTauEval :=
  evalTau precision tau3091 contact3091 logTwoBall

theorem center_sq3091 : (center3091.re : ℝ)^2 +
    (center3091.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3091]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3091 : work3091.theta.ok = true ∧
    work3091.jac.invOK = true ∧ acceptsUnitSq work3091.out = true := by decide +kernel

def cell3091 : CellCertificate where
  tauBall := tau3091
  contactCenter := center3091
  contactBall := contact3091
  work := work3091
  center_sq := center_sq3091
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3091.1
  jac_ok := checks3091.2.1
  accepted := checks3091.2.2

def tau3092 : RatBall :=
  ⟨⟨15/128, -237/640⟩, 3/1280⟩
def center3092 : GaussianRat :=
  ⟨46925291/500000000, -53033649/200000000⟩
def contact3092 : RatBall := localContactBall tau3092 center3092

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386


