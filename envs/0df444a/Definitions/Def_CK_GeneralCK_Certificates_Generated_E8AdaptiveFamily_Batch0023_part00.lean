-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:12:35.322433+00:00
-- url     : https://prove2.me/theorems/192f4158-e0a8-410a-97e7-8cbdffd86767
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0023 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0184 : RatBall :=
  ⟨⟨21/80, -1/80⟩, 3/160⟩
def center0184 : GaussianRat :=
  ⟨4445163/25000000, -8084719/1000000000⟩
def contact0184 : RatBall := localContactBall tau0184 center0184
def work0184 : RoundedTauEval :=
  evalTau precision tau0184 contact0184 logTwoBall

theorem center_sq0184 : (center0184.re : ℝ)^2 +
    (center0184.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0184]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0184 : work0184.theta.ok = true ∧
    work0184.jac.invOK = true ∧ acceptsUnitSq work0184.out = true := by decide +kernel

def cell0184 : CellCertificate where
  tauBall := tau0184
  contactCenter := center0184
  contactBall := contact0184
  work := work0184
  center_sq := center_sq0184
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0184.1
  jac_ok := checks0184.2.1
  accepted := checks0184.2.2

def tau0185 : RatBall :=
  ⟨⟨23/80, -1/80⟩, 3/160⟩
def center0185 : GaussianRat :=
  ⟨7754861/40000000, -3988989/500000000⟩
def contact0185 : RatBall := localContactBall tau0185 center0185
def work0185 : RoundedTauEval :=
  evalTau precision tau0185 contact0185 logTwoBall

theorem center_sq0185 : (center0185.re : ℝ)^2 +
    (center0185.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0185]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0185 : work0185.theta.ok = true ∧
    work0185.jac.invOK = true ∧ acceptsUnitSq work0185.out = true := by decide +kernel

def cell0185 : CellCertificate where
  tauBall := tau0185
  contactCenter := center0185
  contactBall := contact0185
  work := work0185
  center_sq := center_sq0185
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0185.1
  jac_ok := checks0185.2.1
  accepted := checks0185.2.2

def tau0186 : RatBall :=
  ⟨⟨5/16, -7/80⟩, 3/160⟩
def center0186 : GaussianRat :=
  ⟨211121197/1000000000, -55135609/1000000000⟩
def contact0186 : RatBall := localContactBall tau0186 center0186
def work0186 : RoundedTauEval :=
  evalTau precision tau0186 contact0186 logTwoBall

theorem center_sq0186 : (center0186.re : ℝ)^2 +
    (center0186.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0186]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0186 : work0186.theta.ok = true ∧
    work0186.jac.invOK = true ∧ acceptsUnitSq work0186.out = true := by decide +kernel

def cell0186 : CellCertificate where
  tauBall := tau0186
  contactCenter := center0186
  contactBall := contact0186
  work := work0186
  center_sq := center_sq0186
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0186.1
  jac_ok := checks0186.2.1
  accepted := checks0186.2.2

def tau0187 : RatBall :=
  ⟨⟨27/80, -7/80⟩, 3/160⟩
def center0187 : GaussianRat :=
  ⟨14175019/62500000, -54291363/1000000000⟩
def contact0187 : RatBall := localContactBall tau0187 center0187
def work0187 : RoundedTauEval :=
  evalTau precision tau0187 contact0187 logTwoBall

theorem center_sq0187 : (center0187.re : ℝ)^2 +
    (center0187.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0187]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023


