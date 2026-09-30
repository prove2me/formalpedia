-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:59:50.50032+00:00
-- url     : https://prove2.me/theorems/3f44ab87-81aa-4e14-acc1-3c32c85488ca
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0383.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0383_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell3069 : CellCertificate where
  tauBall := tau3069
  contactCenter := center3069
  contactBall := contact3069
  work := work3069
  center_sq := center_sq3069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3069.1
  jac_ok := checks3069.2.1
  accepted := checks3069.2.2

def tau3070 : RatBall :=
  ⟨⟨77/640, -243/640⟩, 3/1280⟩
def center3070 : GaussianRat :=
  ⟨97101919/1000000000, -68076089/250000000⟩
def contact3070 : RatBall := localContactBall tau3070 center3070
def work3070 : RoundedTauEval :=
  evalTau precision tau3070 contact3070 logTwoBall

theorem center_sq3070 : (center3070.re : ℝ)^2 +
    (center3070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3070 : work3070.theta.ok = true ∧
    work3070.jac.invOK = true ∧ acceptsUnitSq work3070.out = true := by decide +kernel

def cell3070 : CellCertificate where
  tauBall := tau3070
  contactCenter := center3070
  contactBall := contact3070
  work := work3070
  center_sq := center_sq3070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3070.1
  jac_ok := checks3070.2.1
  accepted := checks3070.2.2

def tau3071 : RatBall :=
  ⟨⟨79/640, -243/640⟩, 3/1280⟩
def center3071 : GaussianRat :=
  ⟨24893429/250000000, -136015413/500000000⟩
def contact3071 : RatBall := localContactBall tau3071 center3071
def work3071 : RoundedTauEval :=
  evalTau precision tau3071 contact3071 logTwoBall

theorem center_sq3071 : (center3071.re : ℝ)^2 +
    (center3071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3071 : work3071.theta.ok = true ∧
    work3071.jac.invOK = true ∧ acceptsUnitSq work3071.out = true := by decide +kernel

def cell3071 : CellCertificate where
  tauBall := tau3071
  contactCenter := center3071
  contactBall := contact3071
  work := work3071
  center_sq := center_sq3071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3071.1
  jac_ok := checks3071.2.1
  accepted := checks3071.2.2

def cells : List CellCertificate := [cell3064, cell3065, cell3066, cell3067, cell3068, cell3069, cell3070, cell3071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383


