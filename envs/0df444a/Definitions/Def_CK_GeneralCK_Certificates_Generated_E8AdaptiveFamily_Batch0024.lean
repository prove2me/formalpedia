-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:34:32.321159+00:00
-- url     : https://prove2.me/theorems/c6729d5d-4352-4c4e-b50f-3bac4013d41f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0024.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0024_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0198 : (center0198.re : ℝ)^2 +
    (center0198.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0198]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0198 : work0198.theta.ok = true ∧
    work0198.jac.invOK = true ∧ acceptsUnitSq work0198.out = true := by decide +kernel

def cell0198 : CellCertificate where
  tauBall := tau0198
  contactCenter := center0198
  contactBall := contact0198
  work := work0198
  center_sq := center_sq0198
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0198.1
  jac_ok := checks0198.2.1
  accepted := checks0198.2.2

def tau0199 : RatBall :=
  ⟨⟨-29/80, 1/80⟩, 3/160⟩
def center0199 : GaussianRat :=
  ⟨-240695961/1000000000, 1905207/250000000⟩
def contact0199 : RatBall := localContactBall tau0199 center0199
def work0199 : RoundedTauEval :=
  evalTau precision tau0199 contact0199 logTwoBall

theorem center_sq0199 : (center0199.re : ℝ)^2 +
    (center0199.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0199]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0199 : work0199.theta.ok = true ∧
    work0199.jac.invOK = true ∧ acceptsUnitSq work0199.out = true := by decide +kernel

def cell0199 : CellCertificate where
  tauBall := tau0199
  contactCenter := center0199
  contactBall := contact0199
  work := work0199
  center_sq := center_sq0199
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0199.1
  jac_ok := checks0199.2.1
  accepted := checks0199.2.2

def cells : List CellCertificate := [cell0192, cell0193, cell0194, cell0195, cell0196, cell0197, cell0198, cell0199]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024


