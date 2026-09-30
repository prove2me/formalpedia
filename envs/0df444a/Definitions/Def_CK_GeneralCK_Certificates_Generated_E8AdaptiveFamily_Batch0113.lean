-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:56:11.779917+00:00
-- url     : https://prove2.me/theorems/c166980e-d6eb-4da8-804c-75ca39293301
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0113.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0113_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0910 : (center0910.re : ℝ)^2 +
    (center0910.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0910]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0910 : work0910.theta.ok = true ∧
    work0910.jac.invOK = true ∧ acceptsUnitSq work0910.out = true := by decide +kernel

def cell0910 : CellCertificate where
  tauBall := tau0910
  contactCenter := center0910
  contactBall := contact0910
  work := work0910
  center_sq := center_sq0910
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0910.1
  jac_ok := checks0910.2.1
  accepted := checks0910.2.2

def tau0911 : RatBall :=
  ⟨⟨-5/32, 41/160⟩, 3/320⟩
def center0911 : GaussianRat :=
  ⟨-114906151/1000000000, 176804909/1000000000⟩
def contact0911 : RatBall := localContactBall tau0911 center0911
def work0911 : RoundedTauEval :=
  evalTau precision tau0911 contact0911 logTwoBall

theorem center_sq0911 : (center0911.re : ℝ)^2 +
    (center0911.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0911]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0911 : work0911.theta.ok = true ∧
    work0911.jac.invOK = true ∧ acceptsUnitSq work0911.out = true := by decide +kernel

def cell0911 : CellCertificate where
  tauBall := tau0911
  contactCenter := center0911
  contactBall := contact0911
  work := work0911
  center_sq := center_sq0911
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0911.1
  jac_ok := checks0911.2.1
  accepted := checks0911.2.2

def cells : List CellCertificate := [cell0904, cell0905, cell0906, cell0907, cell0908, cell0909, cell0910, cell0911]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113


