-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0419_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:00:53.768953+00:00
-- url     : https://prove2.me/theorems/16812b74-ba91-4752-ba92-9921476b639e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0419 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3352 : RatBall :=
  ⟨⟨-13/128, 243/640⟩, 3/1280⟩
def center3352 : GaussianRat :=
  ⟨-82196967/1000000000, 136904929/500000000⟩
def contact3352 : RatBall := localContactBall tau3352 center3352
def work3352 : RoundedTauEval :=
  evalTau precision tau3352 contact3352 logTwoBall

theorem center_sq3352 : (center3352.re : ℝ)^2 +
    (center3352.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3352]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3352 : work3352.theta.ok = true ∧
    work3352.jac.invOK = true ∧ acceptsUnitSq work3352.out = true := by decide +kernel

def cell3352 : CellCertificate where
  tauBall := tau3352
  contactCenter := center3352
  contactBall := contact3352
  work := work3352
  center_sq := center_sq3352
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3352.1
  jac_ok := checks3352.2.1
  accepted := checks3352.2.2

def tau3353 : RatBall :=
  ⟨⟨-71/640, 49/128⟩, 3/1280⟩
def center3353 : GaussianRat :=
  ⟨-44958767/500000000, 275574013/1000000000⟩
def contact3353 : RatBall := localContactBall tau3353 center3353
def work3353 : RoundedTauEval :=
  evalTau precision tau3353 contact3353 logTwoBall

theorem center_sq3353 : (center3353.re : ℝ)^2 +
    (center3353.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3353]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3353 : work3353.theta.ok = true ∧
    work3353.jac.invOK = true ∧ acceptsUnitSq work3353.out = true := by decide +kernel

def cell3353 : CellCertificate where
  tauBall := tau3353
  contactCenter := center3353
  contactBall := contact3353
  work := work3353
  center_sq := center_sq3353
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3353.1
  jac_ok := checks3353.2.1
  accepted := checks3353.2.2

def tau3354 : RatBall :=
  ⟨⟨-69/640, 49/128⟩, 3/1280⟩
def center3354 : GaussianRat :=
  ⟨-43712483/500000000, 34478141/125000000⟩
def contact3354 : RatBall := localContactBall tau3354 center3354
def work3354 : RoundedTauEval :=
  evalTau precision tau3354 contact3354 logTwoBall

theorem center_sq3354 : (center3354.re : ℝ)^2 +
    (center3354.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3354]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3354 : work3354.theta.ok = true ∧
    work3354.jac.invOK = true ∧ acceptsUnitSq work3354.out = true := by decide +kernel

def cell3354 : CellCertificate where
  tauBall := tau3354
  contactCenter := center3354
  contactBall := contact3354
  work := work3354
  center_sq := center_sq3354
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3354.1
  jac_ok := checks3354.2.1
  accepted := checks3354.2.2

def tau3355 : RatBall :=
  ⟨⟨-71/640, 247/640⟩, 3/1280⟩
def center3355 : GaussianRat :=
  ⟨-90173701/1000000000, 278068181/1000000000⟩
def contact3355 : RatBall := localContactBall tau3355 center3355
def work3355 : RoundedTauEval :=
  evalTau precision tau3355 contact3355 logTwoBall

theorem center_sq3355 : (center3355.re : ℝ)^2 +
    (center3355.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3355]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3355 : work3355.theta.ok = true ∧
    work3355.jac.invOK = true ∧ acceptsUnitSq work3355.out = true := by decide +kernel

def cell3355 : CellCertificate where
  tauBall := tau3355
  contactCenter := center3355
  contactBall := contact3355
  work := work3355
  center_sq := center_sq3355
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3355.1
  jac_ok := checks3355.2.1
  accepted := checks3355.2.2

def tau3356 : RatBall :=
  ⟨⟨-69/640, 247/640⟩, 3/1280⟩
def center3356 : GaussianRat :=
  ⟨-87674459/1000000000, 278322741/1000000000⟩
def contact3356 : RatBall := localContactBall tau3356 center3356

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419


