-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:07:49.571983+00:00
-- url     : https://prove2.me/theorems/c8b20297-e04a-406a-bae7-716f0c9bb755
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0025.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0206 : RatBall :=
  ⟨⟨-27/80, 1/16⟩, 3/160⟩
def center0206 : GaussianRat :=
  ⟨-22606221/100000000, 4844151/125000000⟩
def contact0206 : RatBall := localContactBall tau0206 center0206
def work0206 : RoundedTauEval :=
  evalTau precision tau0206 contact0206 logTwoBall

theorem center_sq0206 : (center0206.re : ℝ)^2 +
    (center0206.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0206]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0206 : work0206.theta.ok = true ∧
    work0206.jac.invOK = true ∧ acceptsUnitSq work0206.out = true := by decide +kernel

def cell0206 : CellCertificate where
  tauBall := tau0206
  contactCenter := center0206
  contactBall := contact0206
  work := work0206
  center_sq := center_sq0206
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0206.1
  jac_ok := checks0206.2.1
  accepted := checks0206.2.2

def tau0207 : RatBall :=
  ⟨⟨-5/16, 1/16⟩, 3/160⟩
def center0207 : GaussianRat :=
  ⟨-26302089/125000000, 3935289/100000000⟩
def contact0207 : RatBall := localContactBall tau0207 center0207
def work0207 : RoundedTauEval :=
  evalTau precision tau0207 contact0207 logTwoBall

theorem center_sq0207 : (center0207.re : ℝ)^2 +
    (center0207.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0207]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0207 : work0207.theta.ok = true ∧
    work0207.jac.invOK = true ∧ acceptsUnitSq work0207.out = true := by decide +kernel

def cell0207 : CellCertificate where
  tauBall := tau0207
  contactCenter := center0207
  contactBall := contact0207
  work := work0207
  center_sq := center_sq0207
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0207.1
  jac_ok := checks0207.2.1
  accepted := checks0207.2.2

def cells : List CellCertificate := [cell0200, cell0201, cell0202, cell0203, cell0204, cell0205, cell0206, cell0207]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025


