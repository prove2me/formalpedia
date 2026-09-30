-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0025_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:20:42.247099+00:00
-- url     : https://prove2.me/theorems/7e2d768d-4f8d-40b3-b642-e56aafe02ded
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0025 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0200 : RatBall :=
  ⟨⟨-29/80, 3/80⟩, 3/160⟩
def center0200 : GaussianRat :=
  ⟨-120475049/500000000, 4573419/200000000⟩
def contact0200 : RatBall := localContactBall tau0200 center0200
def work0200 : RoundedTauEval :=
  evalTau precision tau0200 contact0200 logTwoBall

theorem center_sq0200 : (center0200.re : ℝ)^2 +
    (center0200.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0200]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0200 : work0200.theta.ok = true ∧
    work0200.jac.invOK = true ∧ acceptsUnitSq work0200.out = true := by decide +kernel

def cell0200 : CellCertificate where
  tauBall := tau0200
  contactCenter := center0200
  contactBall := contact0200
  work := work0200
  center_sq := center_sq0200
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0200.1
  jac_ok := checks0200.2.1
  accepted := checks0200.2.2

def tau0201 : RatBall :=
  ⟨⟨-27/80, 1/80⟩, 3/160⟩
def center0201 : GaussianRat :=
  ⟨-45065623/200000000, 7745371/1000000000⟩
def contact0201 : RatBall := localContactBall tau0201 center0201
def work0201 : RoundedTauEval :=
  evalTau precision tau0201 contact0201 logTwoBall

theorem center_sq0201 : (center0201.re : ℝ)^2 +
    (center0201.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0201]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0201 : work0201.theta.ok = true ∧
    work0201.jac.invOK = true ∧ acceptsUnitSq work0201.out = true := by decide +kernel

def cell0201 : CellCertificate where
  tauBall := tau0201
  contactCenter := center0201
  contactBall := contact0201
  work := work0201
  center_sq := center_sq0201
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0201.1
  jac_ok := checks0201.2.1
  accepted := checks0201.2.2

def tau0202 : RatBall :=
  ⟨⟨-5/16, 1/80⟩, 3/160⟩
def center0202 : GaussianRat :=
  ⟨-104858117/500000000, 3932321/500000000⟩
def contact0202 : RatBall := localContactBall tau0202 center0202
def work0202 : RoundedTauEval :=
  evalTau precision tau0202 contact0202 logTwoBall

theorem center_sq0202 : (center0202.re : ℝ)^2 +
    (center0202.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0202]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0202 : work0202.theta.ok = true ∧
    work0202.jac.invOK = true ∧ acceptsUnitSq work0202.out = true := by decide +kernel

def cell0202 : CellCertificate where
  tauBall := tau0202
  contactCenter := center0202
  contactBall := contact0202
  work := work0202
  center_sq := center_sq0202
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0202.1
  jac_ok := checks0202.2.1
  accepted := checks0202.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025


