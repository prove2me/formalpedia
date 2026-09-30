-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0418_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:55.098991+00:00
-- url     : https://prove2.me/theorems/ab8ad206-cdbd-4d27-9b3e-c94fdf34eacf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0418 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3344 : RatBall :=
  ⟨⟨-73/640, 49/128⟩, 3/1280⟩
def center3344 : GaussianRat :=
  ⟨-92406637/1000000000, 275316291/1000000000⟩
def contact3344 : RatBall := localContactBall tau3344 center3344
def work3344 : RoundedTauEval :=
  evalTau precision tau3344 contact3344 logTwoBall

theorem center_sq3344 : (center3344.re : ℝ)^2 +
    (center3344.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3344]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3344 : work3344.theta.ok = true ∧
    work3344.jac.invOK = true ∧ acceptsUnitSq work3344.out = true := by decide +kernel

def cell3344 : CellCertificate where
  tauBall := tau3344
  contactCenter := center3344
  contactBall := contact3344
  work := work3344
  center_sq := center_sq3344
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3344.1
  jac_ok := checks3344.2.1
  accepted := checks3344.2.2

def tau3345 : RatBall :=
  ⟨⟨-71/640, 241/640⟩, 3/1280⟩
def center3345 : GaussianRat :=
  ⟨-89415553/1000000000, 270605413/1000000000⟩
def contact3345 : RatBall := localContactBall tau3345 center3345
def work3345 : RoundedTauEval :=
  evalTau precision tau3345 contact3345 logTwoBall

theorem center_sq3345 : (center3345.re : ℝ)^2 +
    (center3345.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3345]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3345 : work3345.theta.ok = true ∧
    work3345.jac.invOK = true ∧ acceptsUnitSq work3345.out = true := by decide +kernel

def cell3345 : CellCertificate where
  tauBall := tau3345
  contactCenter := center3345
  contactBall := contact3345
  work := work3345
  center_sq := center_sq3345
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3345.1
  jac_ok := checks3345.2.1
  accepted := checks3345.2.2

def tau3346 : RatBall :=
  ⟨⟨-69/640, 241/640⟩, 3/1280⟩
def center3346 : GaussianRat :=
  ⟨-10867009/125000000, 67712443/250000000⟩
def contact3346 : RatBall := localContactBall tau3346 center3346
def work3346 : RoundedTauEval :=
  evalTau precision tau3346 contact3346 logTwoBall

theorem center_sq3346 : (center3346.re : ℝ)^2 +
    (center3346.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3346]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3346 : work3346.theta.ok = true ∧
    work3346.jac.invOK = true ∧ acceptsUnitSq work3346.out = true := by decide +kernel

def cell3346 : CellCertificate where
  tauBall := tau3346
  contactCenter := center3346
  contactBall := contact3346
  work := work3346
  center_sq := center_sq3346
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3346.1
  jac_ok := checks3346.2.1
  accepted := checks3346.2.2

def tau3347 : RatBall :=
  ⟨⟨-71/640, 243/640⟩, 3/1280⟩
def center3347 : GaussianRat :=
  ⟨-89664833/1000000000, 68271613/250000000⟩
def contact3347 : RatBall := localContactBall tau3347 center3347
def work3347 : RoundedTauEval :=
  evalTau precision tau3347 contact3347 logTwoBall

theorem center_sq3347 : (center3347.re : ℝ)^2 +
    (center3347.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3347]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3347 : work3347.theta.ok = true ∧
    work3347.jac.invOK = true ∧ acceptsUnitSq work3347.out = true := by decide +kernel

def cell3347 : CellCertificate where
  tauBall := tau3347
  contactCenter := center3347
  contactBall := contact3347
  work := work3347
  center_sq := center_sq3347
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3347.1
  jac_ok := checks3347.2.1
  accepted := checks3347.2.2

def tau3348 : RatBall :=
  ⟨⟨-69/640, 243/640⟩, 3/1280⟩
def center3348 : GaussianRat :=
  ⟨-87178851/1000000000, 273334167/1000000000⟩
def contact3348 : RatBall := localContactBall tau3348 center3348
def work3348 : RoundedTauEval :=
  evalTau precision tau3348 contact3348 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418


