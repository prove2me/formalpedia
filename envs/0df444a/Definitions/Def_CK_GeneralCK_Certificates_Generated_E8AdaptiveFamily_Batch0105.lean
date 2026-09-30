-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:00:56.031678+00:00
-- url     : https://prove2.me/theorems/d2981c77-2c9a-49f1-980e-67944dc0ef64
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0105.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0846 : (center0846.re : ℝ)^2 +
    (center0846.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0846]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0846 : work0846.theta.ok = true ∧
    work0846.jac.invOK = true ∧ acceptsUnitSq work0846.out = true := by decide +kernel

def cell0846 : CellCertificate where
  tauBall := tau0846
  contactCenter := center0846
  contactBall := contact0846
  work := work0846
  center_sq := center_sq0846
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0846.1
  jac_ok := checks0846.2.1
  accepted := checks0846.2.2

def tau0847 : RatBall :=
  ⟨⟨-39/160, 31/160⟩, 3/320⟩
def center0847 : GaussianRat :=
  ⟨-10728219/62500000, 127685733/1000000000⟩
def contact0847 : RatBall := localContactBall tau0847 center0847
def work0847 : RoundedTauEval :=
  evalTau precision tau0847 contact0847 logTwoBall

theorem center_sq0847 : (center0847.re : ℝ)^2 +
    (center0847.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0847]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0847 : work0847.theta.ok = true ∧
    work0847.jac.invOK = true ∧ acceptsUnitSq work0847.out = true := by decide +kernel

def cell0847 : CellCertificate where
  tauBall := tau0847
  contactCenter := center0847
  contactBall := contact0847
  work := work0847
  center_sq := center_sq0847
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0847.1
  jac_ok := checks0847.2.1
  accepted := checks0847.2.2

def cells : List CellCertificate := [cell0840, cell0841, cell0842, cell0843, cell0844, cell0845, cell0846, cell0847]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105


