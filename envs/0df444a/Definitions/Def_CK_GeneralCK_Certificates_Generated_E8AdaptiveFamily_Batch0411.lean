-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:06.092964+00:00
-- url     : https://prove2.me/theorems/ab95ee26-4480-4f29-bd83-8c7bb4d28df2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0411.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0411_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq3292 : (center3292.re : ℝ)^2 +
    (center3292.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3292]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3292 : work3292.theta.ok = true ∧
    work3292.jac.invOK = true ∧ acceptsUnitSq work3292.out = true := by decide +kernel

def cell3292 : CellCertificate where
  tauBall := tau3292
  contactCenter := center3292
  contactBall := contact3292
  work := work3292
  center_sq := center_sq3292
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3292.1
  jac_ok := checks3292.2.1
  accepted := checks3292.2.2

def tau3293 : RatBall :=
  ⟨⟨-91/640, 239/640⟩, 3/1280⟩
def center3293 : GaussianRat :=
  ⟨-113703619/1000000000, 265378247/1000000000⟩
def contact3293 : RatBall := localContactBall tau3293 center3293
def work3293 : RoundedTauEval :=
  evalTau precision tau3293 contact3293 logTwoBall

theorem center_sq3293 : (center3293.re : ℝ)^2 +
    (center3293.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3293]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3293 : work3293.theta.ok = true ∧
    work3293.jac.invOK = true ∧ acceptsUnitSq work3293.out = true := by decide +kernel

def cell3293 : CellCertificate where
  tauBall := tau3293
  contactCenter := center3293
  contactBall := contact3293
  work := work3293
  center_sq := center_sq3293
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3293.1
  jac_ok := checks3293.2.1
  accepted := checks3293.2.2

def tau3294 : RatBall :=
  ⟨⟨-89/640, 239/640⟩, 3/1280⟩
def center3294 : GaussianRat :=
  ⟨-111267493/1000000000, 265680799/1000000000⟩
def contact3294 : RatBall := localContactBall tau3294 center3294
def work3294 : RoundedTauEval :=
  evalTau precision tau3294 contact3294 logTwoBall

theorem center_sq3294 : (center3294.re : ℝ)^2 +
    (center3294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3294 : work3294.theta.ok = true ∧
    work3294.jac.invOK = true ∧ acceptsUnitSq work3294.out = true := by decide +kernel

def cell3294 : CellCertificate where
  tauBall := tau3294
  contactCenter := center3294
  contactBall := contact3294
  work := work3294
  center_sq := center_sq3294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3294.1
  jac_ok := checks3294.2.1
  accepted := checks3294.2.2

def tau3295 : RatBall :=
  ⟨⟨-87/640, 233/640⟩, 3/1280⟩
def center3295 : GaussianRat :=
  ⟨-10796407/100000000, 129338763/500000000⟩
def contact3295 : RatBall := localContactBall tau3295 center3295
def work3295 : RoundedTauEval :=
  evalTau precision tau3295 contact3295 logTwoBall

theorem center_sq3295 : (center3295.re : ℝ)^2 +
    (center3295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3295 : work3295.theta.ok = true ∧
    work3295.jac.invOK = true ∧ acceptsUnitSq work3295.out = true := by decide +kernel

def cell3295 : CellCertificate where
  tauBall := tau3295
  contactCenter := center3295
  contactBall := contact3295
  work := work3295
  center_sq := center_sq3295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3295.1
  jac_ok := checks3295.2.1
  accepted := checks3295.2.2

def cells : List CellCertificate := [cell3288, cell3289, cell3290, cell3291, cell3292, cell3293, cell3294, cell3295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411


