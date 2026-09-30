-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:27:33.831589+00:00
-- url     : https://prove2.me/theorems/d453ad5a-ed6b-4ddf-af47-2689e0bbbfbf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0099.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0099_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0798 : RatBall :=
  ⟨⟨-59/160, 23/160⟩, 3/320⟩
def center0798 : GaussianRat :=
  ⟨-248760621/1000000000, 43775671/500000000⟩
def contact0798 : RatBall := localContactBall tau0798 center0798
def work0798 : RoundedTauEval :=
  evalTau precision tau0798 contact0798 logTwoBall

theorem center_sq0798 : (center0798.re : ℝ)^2 +
    (center0798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0798 : work0798.theta.ok = true ∧
    work0798.jac.invOK = true ∧ acceptsUnitSq work0798.out = true := by decide +kernel

def cell0798 : CellCertificate where
  tauBall := tau0798
  contactCenter := center0798
  contactBall := contact0798
  work := work0798
  center_sq := center_sq0798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0798.1
  jac_ok := checks0798.2.1
  accepted := checks0798.2.2

def tau0799 : RatBall :=
  ⟨⟨-57/160, 23/160⟩, 3/320⟩
def center0799 : GaussianRat :=
  ⟨-30133041/125000000, 17660441/200000000⟩
def contact0799 : RatBall := localContactBall tau0799 center0799
def work0799 : RoundedTauEval :=
  evalTau precision tau0799 contact0799 logTwoBall

theorem center_sq0799 : (center0799.re : ℝ)^2 +
    (center0799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0799 : work0799.theta.ok = true ∧
    work0799.jac.invOK = true ∧ acceptsUnitSq work0799.out = true := by decide +kernel

def cell0799 : CellCertificate where
  tauBall := tau0799
  contactCenter := center0799
  contactBall := contact0799
  work := work0799
  center_sq := center_sq0799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0799.1
  jac_ok := checks0799.2.1
  accepted := checks0799.2.2

def cells : List CellCertificate := [cell0792, cell0793, cell0794, cell0795, cell0796, cell0797, cell0798, cell0799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099


