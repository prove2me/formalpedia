-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:28:40.305421+00:00
-- url     : https://prove2.me/theorems/a9ba5383-2c74-4837-a1a2-22637801fc09
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0351.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0351_part02

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work2814 : RoundedTauEval :=
  evalTau precision tau2814 contact2814 logTwoBall

theorem center_sq2814 : (center2814.re : ℝ)^2 +
    (center2814.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2814]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2814 : work2814.theta.ok = true ∧
    work2814.jac.invOK = true ∧ acceptsUnitSq work2814.out = true := by decide +kernel

def cell2814 : CellCertificate where
  tauBall := tau2814
  contactCenter := center2814
  contactBall := contact2814
  work := work2814
  center_sq := center_sq2814
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2814.1
  jac_ok := checks2814.2.1
  accepted := checks2814.2.2

def tau2815 : RatBall :=
  ⟨⟨-5/128, -253/640⟩, 3/1280⟩
def center2815 : GaussianRat :=
  ⟨-16138267/500000000, -7246099/25000000⟩
def contact2815 : RatBall := localContactBall tau2815 center2815
def work2815 : RoundedTauEval :=
  evalTau precision tau2815 contact2815 logTwoBall

theorem center_sq2815 : (center2815.re : ℝ)^2 +
    (center2815.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2815]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2815 : work2815.theta.ok = true ∧
    work2815.jac.invOK = true ∧ acceptsUnitSq work2815.out = true := by decide +kernel

def cell2815 : CellCertificate where
  tauBall := tau2815
  contactCenter := center2815
  contactBall := contact2815
  work := work2815
  center_sq := center_sq2815
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2815.1
  jac_ok := checks2815.2.1
  accepted := checks2815.2.2

def cells : List CellCertificate := [cell2808, cell2809, cell2810, cell2811, cell2812, cell2813, cell2814, cell2815]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351


