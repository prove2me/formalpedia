-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0428_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:19:29.456059+00:00
-- url     : https://prove2.me/theorems/3a962034-f4db-4e54-b0da-c05369e148e8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0428 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3424 : RatBall :=
  ⟨⟨-33/640, 247/640⟩, 3/1280⟩
def center3424 : GaussianRat :=
  ⟨-8438273/200000000, 281713577/1000000000⟩
def contact3424 : RatBall := localContactBall tau3424 center3424
def work3424 : RoundedTauEval :=
  evalTau precision tau3424 contact3424 logTwoBall

theorem center_sq3424 : (center3424.re : ℝ)^2 +
    (center3424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3424 : work3424.theta.ok = true ∧
    work3424.jac.invOK = true ∧ acceptsUnitSq work3424.out = true := by decide +kernel

def cell3424 : CellCertificate where
  tauBall := tau3424
  contactCenter := center3424
  contactBall := contact3424
  work := work3424
  center_sq := center_sq3424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3424.1
  jac_ok := checks3424.2.1
  accepted := checks3424.2.2

def tau3425 : RatBall :=
  ⟨⟨-47/640, 249/640⟩, 3/1280⟩
def center3425 : GaussianRat :=
  ⟨-60152449/1000000000, 283205599/1000000000⟩
def contact3425 : RatBall := localContactBall tau3425 center3425
def work3425 : RoundedTauEval :=
  evalTau precision tau3425 contact3425 logTwoBall

theorem center_sq3425 : (center3425.re : ℝ)^2 +
    (center3425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3425 : work3425.theta.ok = true ∧
    work3425.jac.invOK = true ∧ acceptsUnitSq work3425.out = true := by decide +kernel

def cell3425 : CellCertificate where
  tauBall := tau3425
  contactCenter := center3425
  contactBall := contact3425
  work := work3425
  center_sq := center_sq3425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3425.1
  jac_ok := checks3425.2.1
  accepted := checks3425.2.2

def tau3426 : RatBall :=
  ⟨⟨-9/128, 249/640⟩, 3/1280⟩
def center3426 : GaussianRat :=
  ⟨-28805449/500000000, 141689483/500000000⟩
def contact3426 : RatBall := localContactBall tau3426 center3426
def work3426 : RoundedTauEval :=
  evalTau precision tau3426 contact3426 logTwoBall

theorem center_sq3426 : (center3426.re : ℝ)^2 +
    (center3426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3426 : work3426.theta.ok = true ∧
    work3426.jac.invOK = true ∧ acceptsUnitSq work3426.out = true := by decide +kernel

def cell3426 : CellCertificate where
  tauBall := tau3426
  contactCenter := center3426
  contactBall := contact3426
  work := work3426
  center_sq := center_sq3426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3426.1
  jac_ok := checks3426.2.1
  accepted := checks3426.2.2

def tau3427 : RatBall :=
  ⟨⟨-47/640, 251/640⟩, 3/1280⟩
def center3427 : GaussianRat :=
  ⟨-1508267/25000000, 71437399/250000000⟩
def contact3427 : RatBall := localContactBall tau3427 center3427
def work3427 : RoundedTauEval :=
  evalTau precision tau3427 contact3427 logTwoBall

theorem center_sq3427 : (center3427.re : ℝ)^2 +
    (center3427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3427 : work3427.theta.ok = true ∧
    work3427.jac.invOK = true ∧ acceptsUnitSq work3427.out = true := by decide +kernel

def cell3427 : CellCertificate where
  tauBall := tau3427
  contactCenter := center3427
  contactBall := contact3427
  work := work3427
  center_sq := center_sq3427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3427.1
  jac_ok := checks3427.2.1
  accepted := checks3427.2.2

def tau3428 : RatBall :=
  ⟨⟨-9/128, 251/640⟩, 3/1280⟩
def center3428 : GaussianRat :=
  ⟨-57781797/1000000000, 285925371/1000000000⟩
def contact3428 : RatBall := localContactBall tau3428 center3428
def work3428 : RoundedTauEval :=
  evalTau precision tau3428 contact3428 logTwoBall

theorem center_sq3428 : (center3428.re : ℝ)^2 +
    (center3428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3428]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428


