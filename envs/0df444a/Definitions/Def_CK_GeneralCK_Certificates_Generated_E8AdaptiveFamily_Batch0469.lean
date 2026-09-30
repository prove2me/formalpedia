-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:46:03.335412+00:00
-- url     : https://prove2.me/theorems/cf009d2d-77bb-4514-b84f-9c7fcb3e8db9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0469.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0469_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center3758 : GaussianRat :=
  ⟨42585897/500000000, 278570563/1000000000⟩
def contact3758 : RatBall := localContactBall tau3758 center3758
def work3758 : RoundedTauEval :=
  evalTau precision tau3758 contact3758 logTwoBall

theorem center_sq3758 : (center3758.re : ℝ)^2 +
    (center3758.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3758]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3758 : work3758.theta.ok = true ∧
    work3758.jac.invOK = true ∧ acceptsUnitSq work3758.out = true := by decide +kernel

def cell3758 : CellCertificate where
  tauBall := tau3758
  contactCenter := center3758
  contactBall := contact3758
  work := work3758
  center_sq := center_sq3758
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3758.1
  jac_ok := checks3758.2.1
  accepted := checks3758.2.2

def tau3759 : RatBall :=
  ⟨⟨69/640, 49/128⟩, 3/1280⟩
def center3759 : GaussianRat :=
  ⟨43712483/500000000, 34478141/125000000⟩
def contact3759 : RatBall := localContactBall tau3759 center3759
def work3759 : RoundedTauEval :=
  evalTau precision tau3759 contact3759 logTwoBall

theorem center_sq3759 : (center3759.re : ℝ)^2 +
    (center3759.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3759]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3759 : work3759.theta.ok = true ∧
    work3759.jac.invOK = true ∧ acceptsUnitSq work3759.out = true := by decide +kernel

def cell3759 : CellCertificate where
  tauBall := tau3759
  contactCenter := center3759
  contactBall := contact3759
  work := work3759
  center_sq := center_sq3759
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3759.1
  jac_ok := checks3759.2.1
  accepted := checks3759.2.2

def cells : List CellCertificate := [cell3752, cell3753, cell3754, cell3755, cell3756, cell3757, cell3758, cell3759]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469


