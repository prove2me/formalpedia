-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0444_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:10:41.412025+00:00
-- url     : https://prove2.me/theorems/c029661e-b908-4ca5-a3be-15d0b0913015
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0444 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3552 : RatBall :=
  ⟨⟨13/640, 253/640⟩, 3/1280⟩
def center3552 : GaussianRat :=
  ⟨16797323/1000000000, 290291883/1000000000⟩
def contact3552 : RatBall := localContactBall tau3552 center3552
def work3552 : RoundedTauEval :=
  evalTau precision tau3552 contact3552 logTwoBall

theorem center_sq3552 : (center3552.re : ℝ)^2 +
    (center3552.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3552]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3552 : work3552.theta.ok = true ∧
    work3552.jac.invOK = true ∧ acceptsUnitSq work3552.out = true := by decide +kernel

def cell3552 : CellCertificate where
  tauBall := tau3552
  contactCenter := center3552
  contactBall := contact3552
  work := work3552
  center_sq := center_sq3552
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3552.1
  jac_ok := checks3552.2.1
  accepted := checks3552.2.2

def tau3553 : RatBall :=
  ⟨⟨3/128, 253/640⟩, 3/1280⟩
def center3553 : GaussianRat :=
  ⟨19379607/1000000000, 58047357/200000000⟩
def contact3553 : RatBall := localContactBall tau3553 center3553
def work3553 : RoundedTauEval :=
  evalTau precision tau3553 contact3553 logTwoBall

theorem center_sq3553 : (center3553.re : ℝ)^2 +
    (center3553.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3553]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3553 : work3553.theta.ok = true ∧
    work3553.jac.invOK = true ∧ acceptsUnitSq work3553.out = true := by decide +kernel

def cell3553 : CellCertificate where
  tauBall := tau3553
  contactCenter := center3553
  contactBall := contact3553
  work := work3553
  center_sq := center_sq3553
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3553.1
  jac_ok := checks3553.2.1
  accepted := checks3553.2.2

def tau3554 : RatBall :=
  ⟨⟨13/640, 51/128⟩, 3/1280⟩
def center3554 : GaussianRat :=
  ⟨3369771/200000000, 146439243/500000000⟩
def contact3554 : RatBall := localContactBall tau3554 center3554
def work3554 : RoundedTauEval :=
  evalTau precision tau3554 contact3554 logTwoBall

theorem center_sq3554 : (center3554.re : ℝ)^2 +
    (center3554.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3554]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3554 : work3554.theta.ok = true ∧
    work3554.jac.invOK = true ∧ acceptsUnitSq work3554.out = true := by decide +kernel

def cell3554 : CellCertificate where
  tauBall := tau3554
  contactCenter := center3554
  contactBall := contact3554
  work := work3554
  center_sq := center_sq3554
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3554.1
  jac_ok := checks3554.2.1
  accepted := checks3554.2.2

def tau3555 : RatBall :=
  ⟨⟨3/128, 51/128⟩, 3/1280⟩
def center3555 : GaussianRat :=
  ⟨60747/3125000, 58564523/200000000⟩
def contact3555 : RatBall := localContactBall tau3555 center3555
def work3555 : RoundedTauEval :=
  evalTau precision tau3555 contact3555 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444


