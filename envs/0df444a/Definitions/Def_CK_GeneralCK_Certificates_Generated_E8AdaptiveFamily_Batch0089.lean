-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:58:59.797314+00:00
-- url     : https://prove2.me/theorems/1ce05b2f-5516-441f-8c86-46d5ac659e14
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0089.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0718 : RatBall :=
  ⟨⟨11/32, -29/160⟩, 3/320⟩
def center0718 : GaussianRat :=
  ⟨117898859/500000000, -112506293/1000000000⟩
def contact0718 : RatBall := localContactBall tau0718 center0718
def work0718 : RoundedTauEval :=
  evalTau precision tau0718 contact0718 logTwoBall

theorem center_sq0718 : (center0718.re : ℝ)^2 +
    (center0718.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0718]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0718 : work0718.theta.ok = true ∧
    work0718.jac.invOK = true ∧ acceptsUnitSq work0718.out = true := by decide +kernel

def cell0718 : CellCertificate where
  tauBall := tau0718
  contactCenter := center0718
  contactBall := contact0718
  work := work0718
  center_sq := center_sq0718
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0718.1
  jac_ok := checks0718.2.1
  accepted := checks0718.2.2

def tau0719 : RatBall :=
  ⟨⟨49/160, -27/160⟩, 3/320⟩
def center0719 : GaussianRat :=
  ⟨211098659/1000000000, -10718597/100000000⟩
def contact0719 : RatBall := localContactBall tau0719 center0719
def work0719 : RoundedTauEval :=
  evalTau precision tau0719 contact0719 logTwoBall

theorem center_sq0719 : (center0719.re : ℝ)^2 +
    (center0719.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0719]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0719 : work0719.theta.ok = true ∧
    work0719.jac.invOK = true ∧ acceptsUnitSq work0719.out = true := by decide +kernel

def cell0719 : CellCertificate where
  tauBall := tau0719
  contactCenter := center0719
  contactBall := contact0719
  work := work0719
  center_sq := center_sq0719
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0719.1
  jac_ok := checks0719.2.1
  accepted := checks0719.2.2

def cells : List CellCertificate := [cell0712, cell0713, cell0714, cell0715, cell0716, cell0717, cell0718, cell0719]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089


