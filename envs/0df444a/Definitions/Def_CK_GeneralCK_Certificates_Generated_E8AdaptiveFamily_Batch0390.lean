-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0390
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0390
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:50:30.371572+00:00
-- url     : https://prove2.me/theorems/c9036eec-7426-4cc0-a8c4-279292826b1f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0390.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0390_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3126 : (center3126.re : ℝ)^2 +
    (center3126.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3126]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3126 : work3126.theta.ok = true ∧
    work3126.jac.invOK = true ∧ acceptsUnitSq work3126.out = true := by decide +kernel

def cell3126 : CellCertificate where
  tauBall := tau3126
  contactCenter := center3126
  contactBall := contact3126
  work := work3126
  center_sq := center_sq3126
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3126.1
  jac_ok := checks3126.2.1
  accepted := checks3126.2.2

def tau3127 : RatBall :=
  ⟨⟨93/640, -233/640⟩, 3/1280⟩
def center3127 : GaussianRat :=
  ⟨115220153/1000000000, -257805963/1000000000⟩
def contact3127 : RatBall := localContactBall tau3127 center3127
def work3127 : RoundedTauEval :=
  evalTau precision tau3127 contact3127 logTwoBall

theorem center_sq3127 : (center3127.re : ℝ)^2 +
    (center3127.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3127 : work3127.theta.ok = true ∧
    work3127.jac.invOK = true ∧ acceptsUnitSq work3127.out = true := by decide +kernel

def cell3127 : CellCertificate where
  tauBall := tau3127
  contactCenter := center3127
  contactBall := contact3127
  work := work3127
  center_sq := center_sq3127
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3127.1
  jac_ok := checks3127.2.1
  accepted := checks3127.2.2

def cells : List CellCertificate := [cell3120, cell3121, cell3122, cell3123, cell3124, cell3125, cell3126, cell3127]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390


