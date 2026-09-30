-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:00.882038+00:00
-- url     : https://prove2.me/theorems/7ae55b6c-ebcc-494d-977b-83db63527516
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0023 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0023_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0187 : work0187.theta.ok = true ∧
    work0187.jac.invOK = true ∧ acceptsUnitSq work0187.out = true := by decide +kernel

def cell0187 : CellCertificate where
  tauBall := tau0187
  contactCenter := center0187
  contactBall := contact0187
  work := work0187
  center_sq := center_sq0187
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0187.1
  jac_ok := checks0187.2.1
  accepted := checks0187.2.2

def tau0188 : RatBall :=
  ⟨⟨5/16, -1/16⟩, 3/160⟩
def center0188 : GaussianRat :=
  ⟨26302089/125000000, -3935289/100000000⟩
def contact0188 : RatBall := localContactBall tau0188 center0188
def work0188 : RoundedTauEval :=
  evalTau precision tau0188 contact0188 logTwoBall

theorem center_sq0188 : (center0188.re : ℝ)^2 +
    (center0188.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0188]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0188 : work0188.theta.ok = true ∧
    work0188.jac.invOK = true ∧ acceptsUnitSq work0188.out = true := by decide +kernel

def cell0188 : CellCertificate where
  tauBall := tau0188
  contactCenter := center0188
  contactBall := contact0188
  work := work0188
  center_sq := center_sq0188
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0188.1
  jac_ok := checks0188.2.1
  accepted := checks0188.2.2

def tau0189 : RatBall :=
  ⟨⟨27/80, -1/16⟩, 3/160⟩
def center0189 : GaussianRat :=
  ⟨22606221/100000000, -4844151/125000000⟩
def contact0189 : RatBall := localContactBall tau0189 center0189
def work0189 : RoundedTauEval :=
  evalTau precision tau0189 contact0189 logTwoBall

theorem center_sq0189 : (center0189.re : ℝ)^2 +
    (center0189.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0189]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0189 : work0189.theta.ok = true ∧
    work0189.jac.invOK = true ∧ acceptsUnitSq work0189.out = true := by decide +kernel

def cell0189 : CellCertificate where
  tauBall := tau0189
  contactCenter := center0189
  contactBall := contact0189
  work := work0189
  center_sq := center_sq0189
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0189.1
  jac_ok := checks0189.2.1
  accepted := checks0189.2.2

def tau0190 : RatBall :=
  ⟨⟨29/80, -1/16⟩, 3/160⟩
def center0190 : GaussianRat :=
  ⟨241459683/1000000000, -9531797/250000000⟩
def contact0190 : RatBall := localContactBall tau0190 center0190
def work0190 : RoundedTauEval :=
  evalTau precision tau0190 contact0190 logTwoBall

theorem center_sq0190 : (center0190.re : ℝ)^2 +
    (center0190.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0190]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0190 : work0190.theta.ok = true ∧
    work0190.jac.invOK = true ∧ acceptsUnitSq work0190.out = true := by decide +kernel

def cell0190 : CellCertificate where
  tauBall := tau0190
  contactCenter := center0190
  contactBall := contact0190
  work := work0190
  center_sq := center_sq0190
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0190.1
  jac_ok := checks0190.2.1
  accepted := checks0190.2.2

def tau0191 : RatBall :=
  ⟨⟨5/16, -3/80⟩, 3/160⟩
def center0191 : GaussianRat :=
  ⟨209949283/1000000000, -11799931/500000000⟩
def contact0191 : RatBall := localContactBall tau0191 center0191

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023


