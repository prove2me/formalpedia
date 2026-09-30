-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:37:49.937899+00:00
-- url     : https://prove2.me/theorems/c326f067-125e-4d51-97bc-c6a23a656f87
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0124.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0124_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0998 : work0998.theta.ok = true ∧
    work0998.jac.invOK = true ∧ acceptsUnitSq work0998.out = true := by decide +kernel

def cell0998 : CellCertificate where
  tauBall := tau0998
  contactCenter := center0998
  contactBall := contact0998
  work := work0998
  center_sq := center_sq0998
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0998.1
  jac_ok := checks0998.2.1
  accepted := checks0998.2.2

def tau0999 : RatBall :=
  ⟨⟨63/160, 13/160⟩, 3/320⟩
def center0999 : GaussianRat :=
  ⟨260916819/1000000000, 48524207/1000000000⟩
def contact0999 : RatBall := localContactBall tau0999 center0999
def work0999 : RoundedTauEval :=
  evalTau precision tau0999 contact0999 logTwoBall

theorem center_sq0999 : (center0999.re : ℝ)^2 +
    (center0999.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0999]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0999 : work0999.theta.ok = true ∧
    work0999.jac.invOK = true ∧ acceptsUnitSq work0999.out = true := by decide +kernel

def cell0999 : CellCertificate where
  tauBall := tau0999
  contactCenter := center0999
  contactBall := contact0999
  work := work0999
  center_sq := center_sq0999
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0999.1
  jac_ok := checks0999.2.1
  accepted := checks0999.2.2

def cells : List CellCertificate := [cell0992, cell0993, cell0994, cell0995, cell0996, cell0997, cell0998, cell0999]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124


