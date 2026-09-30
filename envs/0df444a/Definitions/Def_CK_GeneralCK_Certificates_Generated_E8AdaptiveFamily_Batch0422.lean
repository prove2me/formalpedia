-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0422
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0422
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:37:08.642998+00:00
-- url     : https://prove2.me/theorems/33ff838b-930a-482d-acd5-4b80e326c78f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0422.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0422_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3382 : (center3382.re : ℝ)^2 +
    (center3382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3382 : work3382.theta.ok = true ∧
    work3382.jac.invOK = true ∧ acceptsUnitSq work3382.out = true := by decide +kernel

def cell3382 : CellCertificate where
  tauBall := tau3382
  contactCenter := center3382
  contactBall := contact3382
  work := work3382
  center_sq := center_sq3382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3382.1
  jac_ok := checks3382.2.1
  accepted := checks3382.2.2

def tau3383 : RatBall :=
  ⟨⟨-51/640, 243/640⟩, 3/1280⟩
def center3383 : GaussianRat :=
  ⟨-32332713/500000000, 275263239/1000000000⟩
def contact3383 : RatBall := localContactBall tau3383 center3383
def work3383 : RoundedTauEval :=
  evalTau precision tau3383 contact3383 logTwoBall

theorem center_sq3383 : (center3383.re : ℝ)^2 +
    (center3383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3383 : work3383.theta.ok = true ∧
    work3383.jac.invOK = true ∧ acceptsUnitSq work3383.out = true := by decide +kernel

def cell3383 : CellCertificate where
  tauBall := tau3383
  contactCenter := center3383
  contactBall := contact3383
  work := work3383
  center_sq := center_sq3383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3383.1
  jac_ok := checks3383.2.1
  accepted := checks3383.2.2

def cells : List CellCertificate := [cell3376, cell3377, cell3378, cell3379, cell3380, cell3381, cell3382, cell3383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422


