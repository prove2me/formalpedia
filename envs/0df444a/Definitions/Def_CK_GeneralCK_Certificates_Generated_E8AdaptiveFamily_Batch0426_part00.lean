-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0426_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:14:36.848649+00:00
-- url     : https://prove2.me/theorems/bf13e815-ef5d-4e9d-9150-2709373578cf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0426 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3408 : RatBall :=
  ⟨⟨-9/128, 243/640⟩, 3/1280⟩
def center3408 : GaussianRat :=
  ⟨-456897/8000000, 17236447/62500000⟩
def contact3408 : RatBall := localContactBall tau3408 center3408
def work3408 : RoundedTauEval :=
  evalTau precision tau3408 contact3408 logTwoBall

theorem center_sq3408 : (center3408.re : ℝ)^2 +
    (center3408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3408 : work3408.theta.ok = true ∧
    work3408.jac.invOK = true ∧ acceptsUnitSq work3408.out = true := by decide +kernel

def cell3408 : CellCertificate where
  tauBall := tau3408
  contactCenter := center3408
  contactBall := contact3408
  work := work3408
  center_sq := center_sq3408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3408.1
  jac_ok := checks3408.2.1
  accepted := checks3408.2.2

def tau3409 : RatBall :=
  ⟨⟨-47/640, 49/128⟩, 3/1280⟩
def center3409 : GaussianRat :=
  ⟨-2392131/40000000, 55627861/200000000⟩
def contact3409 : RatBall := localContactBall tau3409 center3409
def work3409 : RoundedTauEval :=
  evalTau precision tau3409 contact3409 logTwoBall

theorem center_sq3409 : (center3409.re : ℝ)^2 +
    (center3409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3409 : work3409.theta.ok = true ∧
    work3409.jac.invOK = true ∧ acceptsUnitSq work3409.out = true := by decide +kernel

def cell3409 : CellCertificate where
  tauBall := tau3409
  contactCenter := center3409
  contactBall := contact3409
  work := work3409
  center_sq := center_sq3409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3409.1
  jac_ok := checks3409.2.1
  accepted := checks3409.2.2

def tau3410 : RatBall :=
  ⟨⟨-9/128, 49/128⟩, 3/1280⟩
def center3410 : GaussianRat :=
  ⟨-57276093/1000000000, 139153977/500000000⟩
def contact3410 : RatBall := localContactBall tau3410 center3410
def work3410 : RoundedTauEval :=
  evalTau precision tau3410 contact3410 logTwoBall

theorem center_sq3410 : (center3410.re : ℝ)^2 +
    (center3410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3410 : work3410.theta.ok = true ∧
    work3410.jac.invOK = true ∧ acceptsUnitSq work3410.out = true := by decide +kernel

def cell3410 : CellCertificate where
  tauBall := tau3410
  contactCenter := center3410
  contactBall := contact3410
  work := work3410
  center_sq := center_sq3410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3410.1
  jac_ok := checks3410.2.1
  accepted := checks3410.2.2

def tau3411 : RatBall :=
  ⟨⟨-47/640, 247/640⟩, 3/1280⟩
def center3411 : GaussianRat :=
  ⟨-59976659/1000000000, 70167217/250000000⟩
def contact3411 : RatBall := localContactBall tau3411 center3411
def work3411 : RoundedTauEval :=
  evalTau precision tau3411 contact3411 logTwoBall

theorem center_sq3411 : (center3411.re : ℝ)^2 +
    (center3411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3411 : work3411.theta.ok = true ∧
    work3411.jac.invOK = true ∧ acceptsUnitSq work3411.out = true := by decide +kernel

def cell3411 : CellCertificate where
  tauBall := tau3411
  contactCenter := center3411
  contactBall := contact3411
  work := work3411
  center_sq := center_sq3411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3411.1
  jac_ok := checks3411.2.1
  accepted := checks3411.2.2

def tau3412 : RatBall :=
  ⟨⟨-9/128, 247/640⟩, 3/1280⟩
def center3412 : GaussianRat :=
  ⟨-2872117/50000000, 14041993/50000000⟩
def contact3412 : RatBall := localContactBall tau3412 center3412
def work3412 : RoundedTauEval :=
  evalTau precision tau3412 contact3412 logTwoBall

theorem center_sq3412 : (center3412.re : ℝ)^2 +
    (center3412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3412]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426


