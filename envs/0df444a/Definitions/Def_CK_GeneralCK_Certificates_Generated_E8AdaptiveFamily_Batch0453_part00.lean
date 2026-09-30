-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:32:07.330074+00:00
-- url     : https://prove2.me/theorems/0829750b-e691-4754-8feb-227d5c721c8b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0453 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3624 : RatBall :=
  ⟨⟨37/640, 249/640⟩, 3/1280⟩
def center3624 : GaussianRat :=
  ⟨11855567/250000000, 283999143/1000000000⟩
def contact3624 : RatBall := localContactBall tau3624 center3624
def work3624 : RoundedTauEval :=
  evalTau precision tau3624 contact3624 logTwoBall

theorem center_sq3624 : (center3624.re : ℝ)^2 +
    (center3624.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3624]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3624 : work3624.theta.ok = true ∧
    work3624.jac.invOK = true ∧ acceptsUnitSq work3624.out = true := by decide +kernel

def cell3624 : CellCertificate where
  tauBall := tau3624
  contactCenter := center3624
  contactBall := contact3624
  work := work3624
  center_sq := center_sq3624
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3624.1
  jac_ok := checks3624.2.1
  accepted := checks3624.2.2

def tau3625 : RatBall :=
  ⟨⟨39/640, 249/640⟩, 3/1280⟩
def center3625 : GaussianRat :=
  ⟨4997259/100000000, 17740947/62500000⟩
def contact3625 : RatBall := localContactBall tau3625 center3625
def work3625 : RoundedTauEval :=
  evalTau precision tau3625 contact3625 logTwoBall

theorem center_sq3625 : (center3625.re : ℝ)^2 +
    (center3625.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3625]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3625 : work3625.theta.ok = true ∧
    work3625.jac.invOK = true ∧ acceptsUnitSq work3625.out = true := by decide +kernel

def cell3625 : CellCertificate where
  tauBall := tau3625
  contactCenter := center3625
  contactBall := contact3625
  work := work3625
  center_sq := center_sq3625
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3625.1
  jac_ok := checks3625.2.1
  accepted := checks3625.2.2

def tau3626 : RatBall :=
  ⟨⟨37/640, 251/640⟩, 3/1280⟩
def center3626 : GaussianRat :=
  ⟨4756353/100000000, 4477409/15625000⟩
def contact3626 : RatBall := localContactBall tau3626 center3626
def work3626 : RoundedTauEval :=
  evalTau precision tau3626 contact3626 logTwoBall

theorem center_sq3626 : (center3626.re : ℝ)^2 +
    (center3626.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3626]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3626 : work3626.theta.ok = true ∧
    work3626.jac.invOK = true ∧ acceptsUnitSq work3626.out = true := by decide +kernel

def cell3626 : CellCertificate where
  tauBall := tau3626
  contactCenter := center3626
  contactBall := contact3626
  work := work3626
  center_sq := center_sq3626
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3626.1
  jac_ok := checks3626.2.1
  accepted := checks3626.2.2

def tau3627 : RatBall :=
  ⟨⟨39/640, 251/640⟩, 3/1280⟩
def center3627 : GaussianRat :=
  ⟨10024261/200000000, 14320409/50000000⟩
def contact3627 : RatBall := localContactBall tau3627 center3627
def work3627 : RoundedTauEval :=
  evalTau precision tau3627 contact3627 logTwoBall

theorem center_sq3627 : (center3627.re : ℝ)^2 +
    (center3627.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3627]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3627 : work3627.theta.ok = true ∧
    work3627.jac.invOK = true ∧ acceptsUnitSq work3627.out = true := by decide +kernel

def cell3627 : CellCertificate where
  tauBall := tau3627
  contactCenter := center3627
  contactBall := contact3627
  work := work3627
  center_sq := center_sq3627
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3627.1
  jac_ok := checks3627.2.1
  accepted := checks3627.2.2

def tau3628 : RatBall :=
  ⟨⟨33/640, 253/640⟩, 3/1280⟩
def center3628 : GaussianRat :=
  ⟨42570217/1000000000, 144694949/500000000⟩
def contact3628 : RatBall := localContactBall tau3628 center3628
def work3628 : RoundedTauEval :=
  evalTau precision tau3628 contact3628 logTwoBall

theorem center_sq3628 : (center3628.re : ℝ)^2 +
    (center3628.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3628]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3628 : work3628.theta.ok = true ∧
    work3628.jac.invOK = true ∧ acceptsUnitSq work3628.out = true := by decide +kernel

def cell3628 : CellCertificate where
  tauBall := tau3628
  contactCenter := center3628
  contactBall := contact3628
  work := work3628
  center_sq := center_sq3628
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3628.1
  jac_ok := checks3628.2.1
  accepted := checks3628.2.2

def tau3629 : RatBall :=
  ⟨⟨7/128, 253/640⟩, 3/1280⟩
def center3629 : GaussianRat :=
  ⟨9027887/200000000, 289257137/1000000000⟩
def contact3629 : RatBall := localContactBall tau3629 center3629
def work3629 : RoundedTauEval :=
  evalTau precision tau3629 contact3629 logTwoBall

theorem center_sq3629 : (center3629.re : ℝ)^2 +
    (center3629.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3629]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3629 : work3629.theta.ok = true ∧
    work3629.jac.invOK = true ∧ acceptsUnitSq work3629.out = true := by decide +kernel

def cell3629 : CellCertificate where
  tauBall := tau3629
  contactCenter := center3629
  contactBall := contact3629
  work := work3629
  center_sq := center_sq3629
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3629.1
  jac_ok := checks3629.2.1
  accepted := checks3629.2.2

def tau3630 : RatBall :=
  ⟨⟨37/640, 253/640⟩, 3/1280⟩
def center3630 : GaussianRat :=
  ⟨47706761/1000000000, 36139591/125000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453


