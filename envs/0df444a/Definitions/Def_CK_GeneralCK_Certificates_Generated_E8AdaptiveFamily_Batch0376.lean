-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:29:41.906751+00:00
-- url     : https://prove2.me/theorems/fa2794dd-0a5c-458a-9ab5-68929950fb68
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0376.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3014 : (center3014.re : ℝ)^2 +
    (center3014.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3014]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3014 : work3014.theta.ok = true ∧
    work3014.jac.invOK = true ∧ acceptsUnitSq work3014.out = true := by decide +kernel

def cell3014 : CellCertificate where
  tauBall := tau3014
  contactCenter := center3014
  contactBall := contact3014
  work := work3014
  center_sq := center_sq3014
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3014.1
  jac_ok := checks3014.2.1
  accepted := checks3014.2.2

def tau3015 : RatBall :=
  ⟨⟨49/640, -247/640⟩, 3/1280⟩
def center3015 : GaussianRat :=
  ⟨6250857/100000000, -280490707/1000000000⟩
def contact3015 : RatBall := localContactBall tau3015 center3015
def work3015 : RoundedTauEval :=
  evalTau precision tau3015 contact3015 logTwoBall

theorem center_sq3015 : (center3015.re : ℝ)^2 +
    (center3015.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3015]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3015 : work3015.theta.ok = true ∧
    work3015.jac.invOK = true ∧ acceptsUnitSq work3015.out = true := by decide +kernel

def cell3015 : CellCertificate where
  tauBall := tau3015
  contactCenter := center3015
  contactBall := contact3015
  work := work3015
  center_sq := center_sq3015
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3015.1
  jac_ok := checks3015.2.1
  accepted := checks3015.2.2

def cells : List CellCertificate := [cell3008, cell3009, cell3010, cell3011, cell3012, cell3013, cell3014, cell3015]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376


