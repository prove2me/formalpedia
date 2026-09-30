-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:21:57.830481+00:00
-- url     : https://prove2.me/theorems/abb2ec9e-4d2f-4683-91b7-efb102a45d52
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0053 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0053_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0427 : CellCertificate where
  tauBall := tau0427
  contactCenter := center0427
  contactBall := contact0427
  work := work0427
  center_sq := center_sq0427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0427.1
  jac_ok := checks0427.2.1
  accepted := checks0427.2.2

def tau0428 : RatBall :=
  ⟨⟨-1/32, -49/160⟩, 3/320⟩
def center0428 : GaussianRat :=
  ⟨-2398433/100000000, -219339251/1000000000⟩
def contact0428 : RatBall := localContactBall tau0428 center0428
def work0428 : RoundedTauEval :=
  evalTau precision tau0428 contact0428 logTwoBall

theorem center_sq0428 : (center0428.re : ℝ)^2 +
    (center0428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0428 : work0428.theta.ok = true ∧
    work0428.jac.invOK = true ∧ acceptsUnitSq work0428.out = true := by decide +kernel

def cell0428 : CellCertificate where
  tauBall := tau0428
  contactCenter := center0428
  contactBall := contact0428
  work := work0428
  center_sq := center_sq0428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0428.1
  jac_ok := checks0428.2.1
  accepted := checks0428.2.2

def tau0429 : RatBall :=
  ⟨⟨-3/160, -51/160⟩, 3/320⟩
def center0429 : GaussianRat :=
  ⟨-581027/40000000, -57285979/250000000⟩
def contact0429 : RatBall := localContactBall tau0429 center0429
def work0429 : RoundedTauEval :=
  evalTau precision tau0429 contact0429 logTwoBall

theorem center_sq0429 : (center0429.re : ℝ)^2 +
    (center0429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0429 : work0429.theta.ok = true ∧
    work0429.jac.invOK = true ∧ acceptsUnitSq work0429.out = true := by decide +kernel

def cell0429 : CellCertificate where
  tauBall := tau0429
  contactCenter := center0429
  contactBall := contact0429
  work := work0429
  center_sq := center_sq0429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0429.1
  jac_ok := checks0429.2.1
  accepted := checks0429.2.2

def tau0430 : RatBall :=
  ⟨⟨-1/160, -51/160⟩, 3/320⟩
def center0430 : GaussianRat :=
  ⟨-4842747/1000000000, -45846653/200000000⟩
def contact0430 : RatBall := localContactBall tau0430 center0430
def work0430 : RoundedTauEval :=
  evalTau precision tau0430 contact0430 logTwoBall

theorem center_sq0430 : (center0430.re : ℝ)^2 +
    (center0430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0430 : work0430.theta.ok = true ∧
    work0430.jac.invOK = true ∧ acceptsUnitSq work0430.out = true := by decide +kernel

def cell0430 : CellCertificate where
  tauBall := tau0430
  contactCenter := center0430
  contactBall := contact0430
  work := work0430
  center_sq := center_sq0430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0430.1
  jac_ok := checks0430.2.1
  accepted := checks0430.2.2

def tau0431 : RatBall :=
  ⟨⟨-3/160, -49/160⟩, 3/320⟩
def center0431 : GaussianRat :=
  ⟨-14395497/1000000000, -27438463/125000000⟩
def contact0431 : RatBall := localContactBall tau0431 center0431
def work0431 : RoundedTauEval :=
  evalTau precision tau0431 contact0431 logTwoBall

theorem center_sq0431 : (center0431.re : ℝ)^2 +
    (center0431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0431]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053


