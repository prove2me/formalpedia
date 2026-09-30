-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:09:10.575729+00:00
-- url     : https://prove2.me/theorems/85d1752f-53da-437c-b345-45f6e1976bb7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0420.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0420_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3364 : (center3364.re : ℝ)^2 +
    (center3364.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3364]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3364 : work3364.theta.ok = true ∧
    work3364.jac.invOK = true ∧ acceptsUnitSq work3364.out = true := by decide +kernel

def cell3364 : CellCertificate where
  tauBall := tau3364
  contactCenter := center3364
  contactBall := contact3364
  work := work3364
  center_sq := center_sq3364
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3364.1
  jac_ok := checks3364.2.1
  accepted := checks3364.2.2

def tau3365 : RatBall :=
  ⟨⟨-59/640, 241/640⟩, 3/1280⟩
def center3365 : GaussianRat :=
  ⟨-37245497/500000000, 8499173/31250000⟩
def contact3365 : RatBall := localContactBall tau3365 center3365
def work3365 : RoundedTauEval :=
  evalTau precision tau3365 contact3365 logTwoBall

theorem center_sq3365 : (center3365.re : ℝ)^2 +
    (center3365.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3365]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3365 : work3365.theta.ok = true ∧
    work3365.jac.invOK = true ∧ acceptsUnitSq work3365.out = true := by decide +kernel

def cell3365 : CellCertificate where
  tauBall := tau3365
  contactCenter := center3365
  contactBall := contact3365
  work := work3365
  center_sq := center_sq3365
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3365.1
  jac_ok := checks3365.2.1
  accepted := checks3365.2.2

def tau3366 : RatBall :=
  ⟨⟨-57/640, 241/640⟩, 3/1280⟩
def center3366 : GaussianRat :=
  ⟨-1439861/20000000, 68044601/250000000⟩
def contact3366 : RatBall := localContactBall tau3366 center3366
def work3366 : RoundedTauEval :=
  evalTau precision tau3366 contact3366 logTwoBall

theorem center_sq3366 : (center3366.re : ℝ)^2 +
    (center3366.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3366]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3366 : work3366.theta.ok = true ∧
    work3366.jac.invOK = true ∧ acceptsUnitSq work3366.out = true := by decide +kernel

def cell3366 : CellCertificate where
  tauBall := tau3366
  contactCenter := center3366
  contactBall := contact3366
  work := work3366
  center_sq := center_sq3366
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3366.1
  jac_ok := checks3366.2.1
  accepted := checks3366.2.2

def tau3367 : RatBall :=
  ⟨⟨-59/640, 243/640⟩, 3/1280⟩
def center3367 : GaussianRat :=
  ⟨-74700643/1000000000, 13723671/50000000⟩
def contact3367 : RatBall := localContactBall tau3367 center3367
def work3367 : RoundedTauEval :=
  evalTau precision tau3367 contact3367 logTwoBall

theorem center_sq3367 : (center3367.re : ℝ)^2 +
    (center3367.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3367]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3367 : work3367.theta.ok = true ∧
    work3367.jac.invOK = true ∧ acceptsUnitSq work3367.out = true := by decide +kernel

def cell3367 : CellCertificate where
  tauBall := tau3367
  contactCenter := center3367
  contactBall := contact3367
  work := work3367
  center_sq := center_sq3367
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3367.1
  jac_ok := checks3367.2.1
  accepted := checks3367.2.2

def cells : List CellCertificate := [cell3360, cell3361, cell3362, cell3363, cell3364, cell3365, cell3366, cell3367]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420


