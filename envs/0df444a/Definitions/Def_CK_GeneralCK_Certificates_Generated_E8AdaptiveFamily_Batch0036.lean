-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:54:44.722901+00:00
-- url     : https://prove2.me/theorems/54907364-1f51-4064-8342-ecadd8d449af
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0036.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0294 : RatBall :=
  ⟨⟨19/80, 7/80⟩, 3/160⟩
def center0294 : GaussianRat :=
  ⟨162690477/1000000000, 28700003/500000000⟩
def contact0294 : RatBall := localContactBall tau0294 center0294
def work0294 : RoundedTauEval :=
  evalTau precision tau0294 contact0294 logTwoBall

theorem center_sq0294 : (center0294.re : ℝ)^2 +
    (center0294.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0294]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0294 : work0294.theta.ok = true ∧
    work0294.jac.invOK = true ∧ acceptsUnitSq work0294.out = true := by decide +kernel

def cell0294 : CellCertificate where
  tauBall := tau0294
  contactCenter := center0294
  contactBall := contact0294
  work := work0294
  center_sq := center_sq0294
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0294.1
  jac_ok := checks0294.2.1
  accepted := checks0294.2.2

def tau0295 : RatBall :=
  ⟨⟨21/80, 1/16⟩, 3/160⟩
def center0295 : GaussianRat :=
  ⟨35685561/200000000, 40459851/1000000000⟩
def contact0295 : RatBall := localContactBall tau0295 center0295
def work0295 : RoundedTauEval :=
  evalTau precision tau0295 contact0295 logTwoBall

theorem center_sq0295 : (center0295.re : ℝ)^2 +
    (center0295.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0295]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0295 : work0295.theta.ok = true ∧
    work0295.jac.invOK = true ∧ acceptsUnitSq work0295.out = true := by decide +kernel

def cell0295 : CellCertificate where
  tauBall := tau0295
  contactCenter := center0295
  contactBall := contact0295
  work := work0295
  center_sq := center_sq0295
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0295.1
  jac_ok := checks0295.2.1
  accepted := checks0295.2.2

def cells : List CellCertificate := [cell0288, cell0289, cell0290, cell0291, cell0292, cell0293, cell0294, cell0295]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036


