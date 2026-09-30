-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:27:34.182484+00:00
-- url     : https://prove2.me/theorems/533ed984-8dfc-41bb-990e-9837bc1044e6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0007.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0007_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0062 : work0062.theta.ok = true ∧
    work0062.jac.invOK = true ∧ acceptsUnitSq work0062.out = true := by decide +kernel

def cell0062 : CellCertificate where
  tauBall := tau0062
  contactCenter := center0062
  contactBall := contact0062
  work := work0062
  center_sq := center_sq0062
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0062.1
  jac_ok := checks0062.2.1
  accepted := checks0062.2.2

def tau0063 : RatBall :=
  ⟨⟨-1/80, -21/80⟩, 3/160⟩
def center0063 : GaussianRat :=
  ⟨-4665703/500000000, -93227751/500000000⟩
def contact0063 : RatBall := localContactBall tau0063 center0063
def work0063 : RoundedTauEval :=
  evalTau precision tau0063 contact0063 logTwoBall

theorem center_sq0063 : (center0063.re : ℝ)^2 +
    (center0063.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0063]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0063 : work0063.theta.ok = true ∧
    work0063.jac.invOK = true ∧ acceptsUnitSq work0063.out = true := by decide +kernel

def cell0063 : CellCertificate where
  tauBall := tau0063
  contactCenter := center0063
  contactBall := contact0063
  work := work0063
  center_sq := center_sq0063
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0063.1
  jac_ok := checks0063.2.1
  accepted := checks0063.2.2

def cells : List CellCertificate := [cell0056, cell0057, cell0058, cell0059, cell0060, cell0061, cell0062, cell0063]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007


