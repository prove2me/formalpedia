-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:35:30.622472+00:00
-- url     : https://prove2.me/theorems/26da5dd5-decb-4246-8e42-1a3b058d5ec8
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0035 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0280 : RatBall :=
  ⟨⟨11/80, 13/80⟩, 3/160⟩
def center0280 : GaussianRat :=
  ⟨48637291/500000000, 111393603/1000000000⟩
def contact0280 : RatBall := localContactBall tau0280 center0280
def work0280 : RoundedTauEval :=
  evalTau precision tau0280 contact0280 logTwoBall

theorem center_sq0280 : (center0280.re : ℝ)^2 +
    (center0280.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0280]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0280 : work0280.theta.ok = true ∧
    work0280.jac.invOK = true ∧ acceptsUnitSq work0280.out = true := by decide +kernel

def cell0280 : CellCertificate where
  tauBall := tau0280
  contactCenter := center0280
  contactBall := contact0280
  work := work0280
  center_sq := center_sq0280
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0280.1
  jac_ok := checks0280.2.1
  accepted := checks0280.2.2

def tau0281 : RatBall :=
  ⟨⟨9/80, 3/16⟩, 3/160⟩
def center0281 : GaussianRat :=
  ⟨80517041/1000000000, 8110609/62500000⟩
def contact0281 : RatBall := localContactBall tau0281 center0281
def work0281 : RoundedTauEval :=
  evalTau precision tau0281 contact0281 logTwoBall

theorem center_sq0281 : (center0281.re : ℝ)^2 +
    (center0281.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0281]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0281 : work0281.theta.ok = true ∧
    work0281.jac.invOK = true ∧ acceptsUnitSq work0281.out = true := by decide +kernel

def cell0281 : CellCertificate where
  tauBall := tau0281
  contactCenter := center0281
  contactBall := contact0281
  work := work0281
  center_sq := center_sq0281
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0281.1
  jac_ok := checks0281.2.1
  accepted := checks0281.2.2

def tau0282 : RatBall :=
  ⟨⟨11/80, 3/16⟩, 3/160⟩
def center0282 : GaussianRat :=
  ⟨1227011/12500000, 8055803/62500000⟩
def contact0282 : RatBall := localContactBall tau0282 center0282
def work0282 : RoundedTauEval :=
  evalTau precision tau0282 contact0282 logTwoBall

theorem center_sq0282 : (center0282.re : ℝ)^2 +
    (center0282.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0282]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0282 : work0282.theta.ok = true ∧
    work0282.jac.invOK = true ∧ acceptsUnitSq work0282.out = true := by decide +kernel

def cell0282 : CellCertificate where
  tauBall := tau0282
  contactCenter := center0282
  contactBall := contact0282
  work := work0282
  center_sq := center_sq0282
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0282.1
  jac_ok := checks0282.2.1
  accepted := checks0282.2.2

def tau0283 : RatBall :=
  ⟨⟨13/80, 13/80⟩, 3/160⟩
def center0283 : GaussianRat :=
  ⟨114628827/1000000000, 110510723/1000000000⟩
def contact0283 : RatBall := localContactBall tau0283 center0283
def work0283 : RoundedTauEval :=
  evalTau precision tau0283 contact0283 logTwoBall

theorem center_sq0283 : (center0283.re : ℝ)^2 +
    (center0283.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0283]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0283 : work0283.theta.ok = true ∧
    work0283.jac.invOK = true ∧ acceptsUnitSq work0283.out = true := by decide +kernel

def cell0283 : CellCertificate where
  tauBall := tau0283
  contactCenter := center0283
  contactBall := contact0283
  work := work0283
  center_sq := center_sq0283
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0283.1
  jac_ok := checks0283.2.1
  accepted := checks0283.2.2

def tau0284 : RatBall :=
  ⟨⟨3/16, 13/80⟩, 3/160⟩
def center0284 : GaussianRat :=
  ⟨131822371/1000000000, 13687313/125000000⟩
def contact0284 : RatBall := localContactBall tau0284 center0284
def work0284 : RoundedTauEval :=
  evalTau precision tau0284 contact0284 logTwoBall

theorem center_sq0284 : (center0284.re : ℝ)^2 +
    (center0284.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0284]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035


