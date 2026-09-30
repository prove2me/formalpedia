-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0430_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:28:43.337699+00:00
-- url     : https://prove2.me/theorems/f56782c4-4710-4f0f-a6f3-1c6a48a453c2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0430 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3440 : RatBall :=
  ⟨⟨-7/128, 249/640⟩, 3/1280⟩
def center3440 : GaussianRat :=
  ⟨-22435003/500000000, 284135717/1000000000⟩
def contact3440 : RatBall := localContactBall tau3440 center3440
def work3440 : RoundedTauEval :=
  evalTau precision tau3440 contact3440 logTwoBall

theorem center_sq3440 : (center3440.re : ℝ)^2 +
    (center3440.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3440]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3440 : work3440.theta.ok = true ∧
    work3440.jac.invOK = true ∧ acceptsUnitSq work3440.out = true := by decide +kernel

def cell3440 : CellCertificate where
  tauBall := tau3440
  contactCenter := center3440
  contactBall := contact3440
  work := work3440
  center_sq := center_sq3440
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3440.1
  jac_ok := checks3440.2.1
  accepted := checks3440.2.2

def tau3441 : RatBall :=
  ⟨⟨-33/640, 249/640⟩, 3/1280⟩
def center3441 : GaussianRat :=
  ⟨-42315903/1000000000, 284264849/1000000000⟩
def contact3441 : RatBall := localContactBall tau3441 center3441
def work3441 : RoundedTauEval :=
  evalTau precision tau3441 contact3441 logTwoBall

theorem center_sq3441 : (center3441.re : ℝ)^2 +
    (center3441.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3441]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3441 : work3441.theta.ok = true ∧
    work3441.jac.invOK = true ∧ acceptsUnitSq work3441.out = true := by decide +kernel

def cell3441 : CellCertificate where
  tauBall := tau3441
  contactCenter := center3441
  contactBall := contact3441
  work := work3441
  center_sq := center_sq3441
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3441.1
  jac_ok := checks3441.2.1
  accepted := checks3441.2.2

def tau3442 : RatBall :=
  ⟨⟨-7/128, 251/640⟩, 3/1280⟩
def center3442 : GaussianRat :=
  ⟨-45003787/1000000000, 57338531/200000000⟩
def contact3442 : RatBall := localContactBall tau3442 center3442
def work3442 : RoundedTauEval :=
  evalTau precision tau3442 contact3442 logTwoBall

theorem center_sq3442 : (center3442.re : ℝ)^2 +
    (center3442.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3442]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3442 : work3442.theta.ok = true ∧
    work3442.jac.invOK = true ∧ acceptsUnitSq work3442.out = true := by decide +kernel

def cell3442 : CellCertificate where
  tauBall := tau3442
  contactCenter := center3442
  contactBall := contact3442
  work := work3442
  center_sq := center_sq3442
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3442.1
  jac_ok := checks3442.2.1
  accepted := checks3442.2.2

def tau3443 : RatBall :=
  ⟨⟨-33/640, 251/640⟩, 3/1280⟩
def center3443 : GaussianRat :=
  ⟨-42442179/1000000000, 286823589/1000000000⟩
def contact3443 : RatBall := localContactBall tau3443 center3443
def work3443 : RoundedTauEval :=
  evalTau precision tau3443 contact3443 logTwoBall

theorem center_sq3443 : (center3443.re : ℝ)^2 +
    (center3443.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3443]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3443 : work3443.theta.ok = true ∧
    work3443.jac.invOK = true ∧ acceptsUnitSq work3443.out = true := by decide +kernel

def cell3443 : CellCertificate where
  tauBall := tau3443
  contactCenter := center3443
  contactBall := contact3443
  work := work3443
  center_sq := center_sq3443
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3443.1
  jac_ok := checks3443.2.1
  accepted := checks3443.2.2

def tau3444 : RatBall :=
  ⟨⟨-39/640, 253/640⟩, 3/1280⟩
def center3444 : GaussianRat :=
  ⟨-50272091/1000000000, 144484349/500000000⟩
def contact3444 : RatBall := localContactBall tau3444 center3444

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430


