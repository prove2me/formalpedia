-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0416_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:41:27.179676+00:00
-- url     : https://prove2.me/theorems/9feb49c6-925a-4e3a-a038-6438a535138a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0416 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3328 : RatBall :=
  ⟨⟨-87/640, 241/640⟩, 3/1280⟩
def center3328 : GaussianRat :=
  ⟨-109122947/1000000000, 53684517/200000000⟩
def contact3328 : RatBall := localContactBall tau3328 center3328
def work3328 : RoundedTauEval :=
  evalTau precision tau3328 contact3328 logTwoBall

theorem center_sq3328 : (center3328.re : ℝ)^2 +
    (center3328.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3328]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3328 : work3328.theta.ok = true ∧
    work3328.jac.invOK = true ∧ acceptsUnitSq work3328.out = true := by decide +kernel

def cell3328 : CellCertificate where
  tauBall := tau3328
  contactCenter := center3328
  contactBall := contact3328
  work := work3328
  center_sq := center_sq3328
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3328.1
  jac_ok := checks3328.2.1
  accepted := checks3328.2.2

def tau3329 : RatBall :=
  ⟨⟨-17/128, 241/640⟩, 3/1280⟩
def center3329 : GaussianRat :=
  ⟨-53336381/500000000, 268717167/1000000000⟩
def contact3329 : RatBall := localContactBall tau3329 center3329
def work3329 : RoundedTauEval :=
  evalTau precision tau3329 contact3329 logTwoBall

theorem center_sq3329 : (center3329.re : ℝ)^2 +
    (center3329.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3329]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3329 : work3329.theta.ok = true ∧
    work3329.jac.invOK = true ∧ acceptsUnitSq work3329.out = true := by decide +kernel

def cell3329 : CellCertificate where
  tauBall := tau3329
  contactCenter := center3329
  contactBall := contact3329
  work := work3329
  center_sq := center_sq3329
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3329.1
  jac_ok := checks3329.2.1
  accepted := checks3329.2.2

def tau3330 : RatBall :=
  ⟨⟨-83/640, 241/640⟩, 3/1280⟩
def center3330 : GaussianRat :=
  ⟨-104218637/1000000000, 134502819/500000000⟩
def contact3330 : RatBall := localContactBall tau3330 center3330
def work3330 : RoundedTauEval :=
  evalTau precision tau3330 contact3330 logTwoBall

theorem center_sq3330 : (center3330.re : ℝ)^2 +
    (center3330.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3330]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3330 : work3330.theta.ok = true ∧
    work3330.jac.invOK = true ∧ acceptsUnitSq work3330.out = true := by decide +kernel

def cell3330 : CellCertificate where
  tauBall := tau3330
  contactCenter := center3330
  contactBall := contact3330
  work := work3330
  center_sq := center_sq3330
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3330.1
  jac_ok := checks3330.2.1
  accepted := checks3330.2.2

def tau3331 : RatBall :=
  ⟨⟨-81/640, 241/640⟩, 3/1280⟩
def center3331 : GaussianRat :=
  ⟨-101760649/1000000000, 269287947/1000000000⟩
def contact3331 : RatBall := localContactBall tau3331 center3331
def work3331 : RoundedTauEval :=
  evalTau precision tau3331 contact3331 logTwoBall

theorem center_sq3331 : (center3331.re : ℝ)^2 +
    (center3331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3331 : work3331.theta.ok = true ∧
    work3331.jac.invOK = true ∧ acceptsUnitSq work3331.out = true := by decide +kernel

def cell3331 : CellCertificate where
  tauBall := tau3331
  contactCenter := center3331
  contactBall := contact3331
  work := work3331
  center_sq := center_sq3331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3331.1
  jac_ok := checks3331.2.1
  accepted := checks3331.2.2

def tau3332 : RatBall :=
  ⟨⟨-83/640, 243/640⟩, 3/1280⟩
def center3332 : GaussianRat :=
  ⟨-4180239/40000000, 271464801/1000000000⟩
def contact3332 : RatBall := localContactBall tau3332 center3332
def work3332 : RoundedTauEval :=
  evalTau precision tau3332 contact3332 logTwoBall

theorem center_sq3332 : (center3332.re : ℝ)^2 +
    (center3332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3332 : work3332.theta.ok = true ∧
    work3332.jac.invOK = true ∧ acceptsUnitSq work3332.out = true := by decide +kernel

def cell3332 : CellCertificate where
  tauBall := tau3332
  contactCenter := center3332
  contactBall := contact3332
  work := work3332
  center_sq := center_sq3332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3332.1
  jac_ok := checks3332.2.1
  accepted := checks3332.2.2

def tau3333 : RatBall :=
  ⟨⟨-81/640, 243/640⟩, 3/1280⟩
def center3333 : GaussianRat :=
  ⟨-51020881/500000000, 135875479/500000000⟩
def contact3333 : RatBall := localContactBall tau3333 center3333
def work3333 : RoundedTauEval :=
  evalTau precision tau3333 contact3333 logTwoBall

theorem center_sq3333 : (center3333.re : ℝ)^2 +
    (center3333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3333 : work3333.theta.ok = true ∧
    work3333.jac.invOK = true ∧ acceptsUnitSq work3333.out = true := by decide +kernel

def cell3333 : CellCertificate where
  tauBall := tau3333
  contactCenter := center3333
  contactBall := contact3333
  work := work3333
  center_sq := center_sq3333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3333.1
  jac_ok := checks3333.2.1
  accepted := checks3333.2.2

def tau3334 : RatBall :=
  ⟨⟨-79/640, 241/640⟩, 3/1280⟩
def center3334 : GaussianRat :=
  ⟨-99298877/1000000000, 134782023/500000000⟩
def contact3334 : RatBall := localContactBall tau3334 center3334
def work3334 : RoundedTauEval :=
  evalTau precision tau3334 contact3334 logTwoBall

theorem center_sq3334 : (center3334.re : ℝ)^2 +
    (center3334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3334 : work3334.theta.ok = true ∧
    work3334.jac.invOK = true ∧ acceptsUnitSq work3334.out = true := by decide +kernel

def cell3334 : CellCertificate where
  tauBall := tau3334
  contactCenter := center3334
  contactBall := contact3334
  work := work3334
  center_sq := center_sq3334
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3334.1
  jac_ok := checks3334.2.1
  accepted := checks3334.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416


