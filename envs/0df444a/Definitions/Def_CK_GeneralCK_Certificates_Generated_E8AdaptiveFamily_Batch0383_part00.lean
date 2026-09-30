-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:06:48.807439+00:00
-- url     : https://prove2.me/theorems/36cb28dd-7ce5-4fb4-81a5-157f7f4ee433
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0383 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3064 : RatBall :=
  ⟨⟨15/128, -49/128⟩, 3/1280⟩
def center3064 : GaussianRat :=
  ⟨9489219/100000000, -275052007/1000000000⟩
def contact3064 : RatBall := localContactBall tau3064 center3064
def work3064 : RoundedTauEval :=
  evalTau precision tau3064 contact3064 logTwoBall

theorem center_sq3064 : (center3064.re : ℝ)^2 +
    (center3064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3064 : work3064.theta.ok = true ∧
    work3064.jac.invOK = true ∧ acceptsUnitSq work3064.out = true := by decide +kernel

def cell3064 : CellCertificate where
  tauBall := tau3064
  contactCenter := center3064
  contactBall := contact3064
  work := work3064
  center_sq := center_sq3064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3064.1
  jac_ok := checks3064.2.1
  accepted := checks3064.2.2

def tau3065 : RatBall :=
  ⟨⟨77/640, -49/128⟩, 3/1280⟩
def center3065 : GaussianRat :=
  ⟨24343527/250000000, -34347651/125000000⟩
def contact3065 : RatBall := localContactBall tau3065 center3065
def work3065 : RoundedTauEval :=
  evalTau precision tau3065 contact3065 logTwoBall

theorem center_sq3065 : (center3065.re : ℝ)^2 +
    (center3065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3065 : work3065.theta.ok = true ∧
    work3065.jac.invOK = true ∧ acceptsUnitSq work3065.out = true := by decide +kernel

def cell3065 : CellCertificate where
  tauBall := tau3065
  contactCenter := center3065
  contactBall := contact3065
  work := work3065
  center_sq := center_sq3065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3065.1
  jac_ok := checks3065.2.1
  accepted := checks3065.2.2

def tau3066 : RatBall :=
  ⟨⟨73/640, -243/640⟩, 3/1280⟩
def center3066 : GaussianRat :=
  ⟨46073697/500000000, -54566443/200000000⟩
def contact3066 : RatBall := localContactBall tau3066 center3066
def work3066 : RoundedTauEval :=
  evalTau precision tau3066 contact3066 logTwoBall

theorem center_sq3066 : (center3066.re : ℝ)^2 +
    (center3066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3066 : work3066.theta.ok = true ∧
    work3066.jac.invOK = true ∧ acceptsUnitSq work3066.out = true := by decide +kernel

def cell3066 : CellCertificate where
  tauBall := tau3066
  contactCenter := center3066
  contactBall := contact3066
  work := work3066
  center_sq := center_sq3066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3066.1
  jac_ok := checks3066.2.1
  accepted := checks3066.2.2

def tau3067 : RatBall :=
  ⟨⟨15/128, -243/640⟩, 3/1280⟩
def center3067 : GaussianRat :=
  ⟨94626451/1000000000, -272571501/1000000000⟩
def contact3067 : RatBall := localContactBall tau3067 center3067
def work3067 : RoundedTauEval :=
  evalTau precision tau3067 contact3067 logTwoBall

theorem center_sq3067 : (center3067.re : ℝ)^2 +
    (center3067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3067 : work3067.theta.ok = true ∧
    work3067.jac.invOK = true ∧ acceptsUnitSq work3067.out = true := by decide +kernel

def cell3067 : CellCertificate where
  tauBall := tau3067
  contactCenter := center3067
  contactBall := contact3067
  work := work3067
  center_sq := center_sq3067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3067.1
  jac_ok := checks3067.2.1
  accepted := checks3067.2.2

def tau3068 : RatBall :=
  ⟨⟨73/640, -241/640⟩, 3/1280⟩
def center3068 : GaussianRat :=
  ⟨11486457/125000000, -270354617/1000000000⟩
def contact3068 : RatBall := localContactBall tau3068 center3068
def work3068 : RoundedTauEval :=
  evalTau precision tau3068 contact3068 logTwoBall

theorem center_sq3068 : (center3068.re : ℝ)^2 +
    (center3068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3068 : work3068.theta.ok = true ∧
    work3068.jac.invOK = true ∧ acceptsUnitSq work3068.out = true := by decide +kernel

def cell3068 : CellCertificate where
  tauBall := tau3068
  contactCenter := center3068
  contactBall := contact3068
  work := work3068
  center_sq := center_sq3068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3068.1
  jac_ok := checks3068.2.1
  accepted := checks3068.2.2

def tau3069 : RatBall :=
  ⟨⟨15/128, -241/640⟩, 3/1280⟩
def center3069 : GaussianRat :=
  ⟨943643/10000000, -270097427/1000000000⟩
def contact3069 : RatBall := localContactBall tau3069 center3069
def work3069 : RoundedTauEval :=
  evalTau precision tau3069 contact3069 logTwoBall

theorem center_sq3069 : (center3069.re : ℝ)^2 +
    (center3069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3069 : work3069.theta.ok = true ∧
    work3069.jac.invOK = true ∧ acceptsUnitSq work3069.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383


