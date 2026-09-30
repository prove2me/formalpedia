-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0417_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:34:22.197825+00:00
-- url     : https://prove2.me/theorems/e0002151-6f41-428c-a56b-9036c8b31f74
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0417 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3336 : RatBall :=
  ⟨⟨-79/640, 243/640⟩, 3/1280⟩
def center3336 : GaussianRat :=
  ⟨-24893429/250000000, 136015413/500000000⟩
def contact3336 : RatBall := localContactBall tau3336 center3336
def work3336 : RoundedTauEval :=
  evalTau precision tau3336 contact3336 logTwoBall

theorem center_sq3336 : (center3336.re : ℝ)^2 +
    (center3336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3336 : work3336.theta.ok = true ∧
    work3336.jac.invOK = true ∧ acceptsUnitSq work3336.out = true := by decide +kernel

def cell3336 : CellCertificate where
  tauBall := tau3336
  contactCenter := center3336
  contactBall := contact3336
  work := work3336
  center_sq := center_sq3336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3336.1
  jac_ok := checks3336.2.1
  accepted := checks3336.2.2

def tau3337 : RatBall :=
  ⟨⟨-77/640, 243/640⟩, 3/1280⟩
def center3337 : GaussianRat :=
  ⟨-97101919/1000000000, 68076089/250000000⟩
def contact3337 : RatBall := localContactBall tau3337 center3337
def work3337 : RoundedTauEval :=
  evalTau precision tau3337 contact3337 logTwoBall

theorem center_sq3337 : (center3337.re : ℝ)^2 +
    (center3337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3337 : work3337.theta.ok = true ∧
    work3337.jac.invOK = true ∧ acceptsUnitSq work3337.out = true := by decide +kernel

def cell3337 : CellCertificate where
  tauBall := tau3337
  contactCenter := center3337
  contactBall := contact3337
  work := work3337
  center_sq := center_sq3337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3337.1
  jac_ok := checks3337.2.1
  accepted := checks3337.2.2

def tau3338 : RatBall :=
  ⟨⟨-15/128, 241/640⟩, 3/1280⟩
def center3338 : GaussianRat :=
  ⟨-943643/10000000, 270097427/1000000000⟩
def contact3338 : RatBall := localContactBall tau3338 center3338
def work3338 : RoundedTauEval :=
  evalTau precision tau3338 contact3338 logTwoBall

theorem center_sq3338 : (center3338.re : ℝ)^2 +
    (center3338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3338 : work3338.theta.ok = true ∧
    work3338.jac.invOK = true ∧ acceptsUnitSq work3338.out = true := by decide +kernel

def cell3338 : CellCertificate where
  tauBall := tau3338
  contactCenter := center3338
  contactBall := contact3338
  work := work3338
  center_sq := center_sq3338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3338.1
  jac_ok := checks3338.2.1
  accepted := checks3338.2.2

def tau3339 : RatBall :=
  ⟨⟨-73/640, 241/640⟩, 3/1280⟩
def center3339 : GaussianRat :=
  ⟨-11486457/125000000, 270354617/1000000000⟩
def contact3339 : RatBall := localContactBall tau3339 center3339
def work3339 : RoundedTauEval :=
  evalTau precision tau3339 contact3339 logTwoBall

theorem center_sq3339 : (center3339.re : ℝ)^2 +
    (center3339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3339 : work3339.theta.ok = true ∧
    work3339.jac.invOK = true ∧ acceptsUnitSq work3339.out = true := by decide +kernel

def cell3339 : CellCertificate where
  tauBall := tau3339
  contactCenter := center3339
  contactBall := contact3339
  work := work3339
  center_sq := center_sq3339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3339.1
  jac_ok := checks3339.2.1
  accepted := checks3339.2.2

def tau3340 : RatBall :=
  ⟨⟨-15/128, 243/640⟩, 3/1280⟩
def center3340 : GaussianRat :=
  ⟨-94626451/1000000000, 272571501/1000000000⟩
def contact3340 : RatBall := localContactBall tau3340 center3340

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417


