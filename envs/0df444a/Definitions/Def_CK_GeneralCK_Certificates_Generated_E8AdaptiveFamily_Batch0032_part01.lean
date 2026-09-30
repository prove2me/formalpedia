-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:31.428273+00:00
-- url     : https://prove2.me/theorems/d15d2ced-0acf-43ef-82e4-ef7be4775a0c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0032 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0258 : CellCertificate where
  tauBall := tau0258
  contactCenter := center0258
  contactBall := contact0258
  work := work0258
  center_sq := center_sq0258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0258.1
  jac_ok := checks0258.2.1
  accepted := checks0258.2.2

def tau0259 : RatBall :=
  ⟨⟨-7/80, 19/80⟩, 3/160⟩
def center0259 : GaussianRat :=
  ⟨-32100469/500000000, 83247331/500000000⟩
def contact0259 : RatBall := localContactBall tau0259 center0259
def work0259 : RoundedTauEval :=
  evalTau precision tau0259 contact0259 logTwoBall

theorem center_sq0259 : (center0259.re : ℝ)^2 +
    (center0259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0259 : work0259.theta.ok = true ∧
    work0259.jac.invOK = true ∧ acceptsUnitSq work0259.out = true := by decide +kernel

def cell0259 : CellCertificate where
  tauBall := tau0259
  contactCenter := center0259
  contactBall := contact0259
  work := work0259
  center_sq := center_sq0259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0259.1
  jac_ok := checks0259.2.1
  accepted := checks0259.2.2

def tau0260 : RatBall :=
  ⟨⟨-1/16, 19/80⟩, 3/160⟩
def center0260 : GaussianRat :=
  ⟨-45935893/1000000000, 836037/5000000⟩
def contact0260 : RatBall := localContactBall tau0260 center0260
def work0260 : RoundedTauEval :=
  evalTau precision tau0260 contact0260 logTwoBall

theorem center_sq0260 : (center0260.re : ℝ)^2 +
    (center0260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0260 : work0260.theta.ok = true ∧
    work0260.jac.invOK = true ∧ acceptsUnitSq work0260.out = true := by decide +kernel

def cell0260 : CellCertificate where
  tauBall := tau0260
  contactCenter := center0260
  contactBall := contact0260
  work := work0260
  center_sq := center_sq0260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0260.1
  jac_ok := checks0260.2.1
  accepted := checks0260.2.2

def tau0261 : RatBall :=
  ⟨⟨-3/80, 17/80⟩, 3/160⟩
def center0261 : GaussianRat :=
  ⟨-13627917/500000000, 149428611/1000000000⟩
def contact0261 : RatBall := localContactBall tau0261 center0261
def work0261 : RoundedTauEval :=
  evalTau precision tau0261 contact0261 logTwoBall

theorem center_sq0261 : (center0261.re : ℝ)^2 +
    (center0261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0261]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032


