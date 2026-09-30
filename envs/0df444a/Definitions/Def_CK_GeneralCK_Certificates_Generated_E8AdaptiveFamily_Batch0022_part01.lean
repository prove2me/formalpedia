-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:05:30.477007+00:00
-- url     : https://prove2.me/theorems/ed1c9349-a543-4f41-9b87-af5ebb3301b1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0022 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0022_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0179 : CellCertificate where
  tauBall := tau0179
  contactCenter := center0179
  contactBall := contact0179
  work := work0179
  center_sq := center_sq0179
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0179.1
  jac_ok := checks0179.2.1
  accepted := checks0179.2.2

def tau0180 : RatBall :=
  ⟨⟨21/80, -1/16⟩, 3/160⟩
def center0180 : GaussianRat :=
  ⟨35685561/200000000, -40459851/1000000000⟩
def contact0180 : RatBall := localContactBall tau0180 center0180
def work0180 : RoundedTauEval :=
  evalTau precision tau0180 contact0180 logTwoBall

theorem center_sq0180 : (center0180.re : ℝ)^2 +
    (center0180.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0180]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0180 : work0180.theta.ok = true ∧
    work0180.jac.invOK = true ∧ acceptsUnitSq work0180.out = true := by decide +kernel

def cell0180 : CellCertificate where
  tauBall := tau0180
  contactCenter := center0180
  contactBall := contact0180
  work := work0180
  center_sq := center_sq0180
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0180.1
  jac_ok := checks0180.2.1
  accepted := checks0180.2.2

def tau0181 : RatBall :=
  ⟨⟨23/80, -1/16⟩, 3/160⟩
def center0181 : GaussianRat :=
  ⟨194534387/1000000000, -7984577/200000000⟩
def contact0181 : RatBall := localContactBall tau0181 center0181
def work0181 : RoundedTauEval :=
  evalTau precision tau0181 contact0181 logTwoBall

theorem center_sq0181 : (center0181.re : ℝ)^2 +
    (center0181.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0181]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0181 : work0181.theta.ok = true ∧
    work0181.jac.invOK = true ∧ acceptsUnitSq work0181.out = true := by decide +kernel

def cell0181 : CellCertificate where
  tauBall := tau0181
  contactCenter := center0181
  contactBall := contact0181
  work := work0181
  center_sq := center_sq0181
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0181.1
  jac_ok := checks0181.2.1
  accepted := checks0181.2.2

def tau0182 : RatBall :=
  ⟨⟨21/80, -3/80⟩, 3/160⟩
def center0182 : GaussianRat :=
  ⟨89006593/500000000, -4852281/200000000⟩
def contact0182 : RatBall := localContactBall tau0182 center0182
def work0182 : RoundedTauEval :=
  evalTau precision tau0182 contact0182 logTwoBall

theorem center_sq0182 : (center0182.re : ℝ)^2 +
    (center0182.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0182]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0182 : work0182.theta.ok = true ∧
    work0182.jac.invOK = true ∧ acceptsUnitSq work0182.out = true := by decide +kernel

def cell0182 : CellCertificate where
  tauBall := tau0182
  contactCenter := center0182
  contactBall := contact0182
  work := work0182
  center_sq := center_sq0182
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0182.1
  jac_ok := checks0182.2.1
  accepted := checks0182.2.2

def tau0183 : RatBall :=
  ⟨⟨23/80, -3/80⟩, 3/160⟩
def center0183 : GaussianRat :=
  ⟨4852301/25000000, -23940531/1000000000⟩
def contact0183 : RatBall := localContactBall tau0183 center0183
def work0183 : RoundedTauEval :=
  evalTau precision tau0183 contact0183 logTwoBall

theorem center_sq0183 : (center0183.re : ℝ)^2 +
    (center0183.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0183]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022


