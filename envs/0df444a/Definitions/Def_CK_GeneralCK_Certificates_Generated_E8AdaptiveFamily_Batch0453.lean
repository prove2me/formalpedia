-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:01:11.210815+00:00
-- url     : https://prove2.me/theorems/b9b1df73-9715-4b0f-8324-c32d72e9a1ec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0453.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0453_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact3630 : RatBall := localContactBall tau3630 center3630
def work3630 : RoundedTauEval :=
  evalTau precision tau3630 contact3630 logTwoBall

theorem center_sq3630 : (center3630.re : ℝ)^2 +
    (center3630.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3630]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3630 : work3630.theta.ok = true ∧
    work3630.jac.invOK = true ∧ acceptsUnitSq work3630.out = true := by decide +kernel

def cell3630 : CellCertificate where
  tauBall := tau3630
  contactCenter := center3630
  contactBall := contact3630
  work := work3630
  center_sq := center_sq3630
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3630.1
  jac_ok := checks3630.2.1
  accepted := checks3630.2.2

def tau3631 : RatBall :=
  ⟨⟨39/640, 253/640⟩, 3/1280⟩
def center3631 : GaussianRat :=
  ⟨50272091/1000000000, 144484349/500000000⟩
def contact3631 : RatBall := localContactBall tau3631 center3631
def work3631 : RoundedTauEval :=
  evalTau precision tau3631 contact3631 logTwoBall

theorem center_sq3631 : (center3631.re : ℝ)^2 +
    (center3631.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3631]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3631 : work3631.theta.ok = true ∧
    work3631.jac.invOK = true ∧ acceptsUnitSq work3631.out = true := by decide +kernel

def cell3631 : CellCertificate where
  tauBall := tau3631
  contactCenter := center3631
  contactBall := contact3631
  work := work3631
  center_sq := center_sq3631
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3631.1
  jac_ok := checks3631.2.1
  accepted := checks3631.2.2

def cells : List CellCertificate := [cell3624, cell3625, cell3626, cell3627, cell3628, cell3629, cell3630, cell3631]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453


