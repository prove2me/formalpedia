-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:09:09.229654+00:00
-- url     : https://prove2.me/theorems/56f69363-3ce2-49db-98cc-1684d2c381af
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0310 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2480 : RatBall :=
  ⟨⟨81/320, 93/320⟩, 3/640⟩
def center2480 : GaussianRat :=
  ⟨93152319/500000000, 24105877/125000000⟩
def contact2480 : RatBall := localContactBall tau2480 center2480
def work2480 : RoundedTauEval :=
  evalTau precision tau2480 contact2480 logTwoBall

theorem center_sq2480 : (center2480.re : ℝ)^2 +
    (center2480.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2480]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2480 : work2480.theta.ok = true ∧
    work2480.jac.invOK = true ∧ acceptsUnitSq work2480.out = true := by decide +kernel

def cell2480 : CellCertificate where
  tauBall := tau2480
  contactCenter := center2480
  contactBall := contact2480
  work := work2480
  center_sq := center_sq2480
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2480.1
  jac_ok := checks2480.2.1
  accepted := checks2480.2.2

def tau2481 : RatBall :=
  ⟨⟨83/320, 93/320⟩, 3/640⟩
def center2481 : GaussianRat :=
  ⟨95308733/500000000, 192166077/1000000000⟩
def contact2481 : RatBall := localContactBall tau2481 center2481
def work2481 : RoundedTauEval :=
  evalTau precision tau2481 contact2481 logTwoBall

theorem center_sq2481 : (center2481.re : ℝ)^2 +
    (center2481.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2481]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2481 : work2481.theta.ok = true ∧
    work2481.jac.invOK = true ∧ acceptsUnitSq work2481.out = true := by decide +kernel

def cell2481 : CellCertificate where
  tauBall := tau2481
  contactCenter := center2481
  contactBall := contact2481
  work := work2481
  center_sq := center_sq2481
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2481.1
  jac_ok := checks2481.2.1
  accepted := checks2481.2.2

def tau2482 : RatBall :=
  ⟨⟨81/320, 19/64⟩, 3/640⟩
def center2482 : GaussianRat :=
  ⟨186989333/1000000000, 49293783/250000000⟩
def contact2482 : RatBall := localContactBall tau2482 center2482
def work2482 : RoundedTauEval :=
  evalTau precision tau2482 contact2482 logTwoBall

theorem center_sq2482 : (center2482.re : ℝ)^2 +
    (center2482.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2482]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2482 : work2482.theta.ok = true ∧
    work2482.jac.invOK = true ∧ acceptsUnitSq work2482.out = true := by decide +kernel

def cell2482 : CellCertificate where
  tauBall := tau2482
  contactCenter := center2482
  contactBall := contact2482
  work := work2482
  center_sq := center_sq2482
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2482.1
  jac_ok := checks2482.2.1
  accepted := checks2482.2.2

def tau2483 : RatBall :=
  ⟨⟨83/320, 19/64⟩, 3/640⟩
def center2483 : GaussianRat :=
  ⟨191313683/1000000000, 3929501/20000000⟩
def contact2483 : RatBall := localContactBall tau2483 center2483
def work2483 : RoundedTauEval :=
  evalTau precision tau2483 contact2483 logTwoBall

theorem center_sq2483 : (center2483.re : ℝ)^2 +
    (center2483.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2483]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2483 : work2483.theta.ok = true ∧
    work2483.jac.invOK = true ∧ acceptsUnitSq work2483.out = true := by decide +kernel

def cell2483 : CellCertificate where
  tauBall := tau2483
  contactCenter := center2483
  contactBall := contact2483
  work := work2483
  center_sq := center_sq2483
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2483.1
  jac_ok := checks2483.2.1
  accepted := checks2483.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310


