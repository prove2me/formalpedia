-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:49:55.502517+00:00
-- url     : https://prove2.me/theorems/41ca460c-0845-4495-b99a-a3e7b2287de3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0464.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0464_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3718 : GaussianRat :=
  ⟨25844903/250000000, 261664807/1000000000⟩
def contact3718 : RatBall := localContactBall tau3718 center3718
def work3718 : RoundedTauEval :=
  evalTau precision tau3718 contact3718 logTwoBall

theorem center_sq3718 : (center3718.re : ℝ)^2 +
    (center3718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3718 : work3718.theta.ok = true ∧
    work3718.jac.invOK = true ∧ acceptsUnitSq work3718.out = true := by decide +kernel

def cell3718 : CellCertificate where
  tauBall := tau3718
  contactCenter := center3718
  contactBall := contact3718
  work := work3718
  center_sq := center_sq3718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3718.1
  jac_ok := checks3718.2.1
  accepted := checks3718.2.2

def tau3719 : RatBall :=
  ⟨⟨17/128, 233/640⟩, 3/1280⟩
def center3719 : GaussianRat :=
  ⟨105537631/1000000000, 258956581/1000000000⟩
def contact3719 : RatBall := localContactBall tau3719 center3719
def work3719 : RoundedTauEval :=
  evalTau precision tau3719 contact3719 logTwoBall

theorem center_sq3719 : (center3719.re : ℝ)^2 +
    (center3719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3719 : work3719.theta.ok = true ∧
    work3719.jac.invOK = true ∧ acceptsUnitSq work3719.out = true := by decide +kernel

def cell3719 : CellCertificate where
  tauBall := tau3719
  contactCenter := center3719
  contactBall := contact3719
  work := work3719
  center_sq := center_sq3719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3719.1
  jac_ok := checks3719.2.1
  accepted := checks3719.2.2

def cells : List CellCertificate := [cell3712, cell3713, cell3714, cell3715, cell3716, cell3717, cell3718, cell3719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464


