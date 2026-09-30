-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:40:03.082767+00:00
-- url     : https://prove2.me/theorems/13095d19-4bc3-4170-8823-79be65891e4b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0108.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0108_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0870 : RatBall :=
  ⟨⟨-39/160, 33/160⟩, 3/320⟩
def center0870 : GaussianRat :=
  ⟨-172488051/1000000000, 136096987/1000000000⟩
def contact0870 : RatBall := localContactBall tau0870 center0870
def work0870 : RoundedTauEval :=
  evalTau precision tau0870 contact0870 logTwoBall

theorem center_sq0870 : (center0870.re : ℝ)^2 +
    (center0870.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0870]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0870 : work0870.theta.ok = true ∧
    work0870.jac.invOK = true ∧ acceptsUnitSq work0870.out = true := by decide +kernel

def cell0870 : CellCertificate where
  tauBall := tau0870
  contactCenter := center0870
  contactBall := contact0870
  work := work0870
  center_sq := center_sq0870
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0870.1
  jac_ok := checks0870.2.1
  accepted := checks0870.2.2

def tau0871 : RatBall :=
  ⟨⟨-37/160, 33/160⟩, 3/320⟩
def center0871 : GaussianRat :=
  ⟨-164030831/1000000000, 3423667/25000000⟩
def contact0871 : RatBall := localContactBall tau0871 center0871
def work0871 : RoundedTauEval :=
  evalTau precision tau0871 contact0871 logTwoBall

theorem center_sq0871 : (center0871.re : ℝ)^2 +
    (center0871.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0871]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0871 : work0871.theta.ok = true ∧
    work0871.jac.invOK = true ∧ acceptsUnitSq work0871.out = true := by decide +kernel

def cell0871 : CellCertificate where
  tauBall := tau0871
  contactCenter := center0871
  contactBall := contact0871
  work := work0871
  center_sq := center_sq0871
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0871.1
  jac_ok := checks0871.2.1
  accepted := checks0871.2.2

def cells : List CellCertificate := [cell0864, cell0865, cell0866, cell0867, cell0868, cell0869, cell0870, cell0871]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108


