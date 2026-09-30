-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0315_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:29.100508+00:00
-- url     : https://prove2.me/theorems/04974d50-d5fb-40a9-8317-b056bbe10e1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0315 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2520 : RatBall :=
  ⟨⟨13/64, 97/320⟩, 3/640⟩
def center2520 : GaussianRat :=
  ⟨9520441/62500000, 206807941/1000000000⟩
def contact2520 : RatBall := localContactBall tau2520 center2520
def work2520 : RoundedTauEval :=
  evalTau precision tau2520 contact2520 logTwoBall

theorem center_sq2520 : (center2520.re : ℝ)^2 +
    (center2520.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2520]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2520 : work2520.theta.ok = true ∧
    work2520.jac.invOK = true ∧ acceptsUnitSq work2520.out = true := by decide +kernel

def cell2520 : CellCertificate where
  tauBall := tau2520
  contactCenter := center2520
  contactBall := contact2520
  work := work2520
  center_sq := center_sq2520
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2520.1
  jac_ok := checks2520.2.1
  accepted := checks2520.2.2

def tau2521 : RatBall :=
  ⟨⟨67/320, 97/320⟩, 3/640⟩
def center2521 : GaussianRat :=
  ⟨19601337/125000000, 103097251/500000000⟩
def contact2521 : RatBall := localContactBall tau2521 center2521
def work2521 : RoundedTauEval :=
  evalTau precision tau2521 contact2521 logTwoBall

theorem center_sq2521 : (center2521.re : ℝ)^2 +
    (center2521.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2521]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2521 : work2521.theta.ok = true ∧
    work2521.jac.invOK = true ∧ acceptsUnitSq work2521.out = true := by decide +kernel

def cell2521 : CellCertificate where
  tauBall := tau2521
  contactCenter := center2521
  contactBall := contact2521
  work := work2521
  center_sq := center_sq2521
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2521.1
  jac_ok := checks2521.2.1
  accepted := checks2521.2.2

def tau2522 : RatBall :=
  ⟨⟨13/64, 99/320⟩, 3/640⟩
def center2522 : GaussianRat :=
  ⟨30588339/200000000, 211307539/1000000000⟩
def contact2522 : RatBall := localContactBall tau2522 center2522
def work2522 : RoundedTauEval :=
  evalTau precision tau2522 contact2522 logTwoBall

theorem center_sq2522 : (center2522.re : ℝ)^2 +
    (center2522.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2522]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2522 : work2522.theta.ok = true ∧
    work2522.jac.invOK = true ∧ acceptsUnitSq work2522.out = true := by decide +kernel

def cell2522 : CellCertificate where
  tauBall := tau2522
  contactCenter := center2522
  contactBall := contact2522
  work := work2522
  center_sq := center_sq2522
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2522.1
  jac_ok := checks2522.2.1
  accepted := checks2522.2.2

def tau2523 : RatBall :=
  ⟨⟨67/320, 99/320⟩, 3/640⟩
def center2523 : GaussianRat :=
  ⟨157440099/1000000000, 210676827/1000000000⟩
def contact2523 : RatBall := localContactBall tau2523 center2523
def work2523 : RoundedTauEval :=
  evalTau precision tau2523 contact2523 logTwoBall

theorem center_sq2523 : (center2523.re : ℝ)^2 +
    (center2523.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2523]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2523 : work2523.theta.ok = true ∧
    work2523.jac.invOK = true ∧ acceptsUnitSq work2523.out = true := by decide +kernel

def cell2523 : CellCertificate where
  tauBall := tau2523
  contactCenter := center2523
  contactBall := contact2523
  work := work2523
  center_sq := center_sq2523
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2523.1
  jac_ok := checks2523.2.1
  accepted := checks2523.2.2

def tau2524 : RatBall :=
  ⟨⟨69/320, 97/320⟩, 3/640⟩
def center2524 : GaussianRat :=
  ⟨161277047/1000000000, 51391661/250000000⟩
def contact2524 : RatBall := localContactBall tau2524 center2524
def work2524 : RoundedTauEval :=
  evalTau precision tau2524 contact2524 logTwoBall

theorem center_sq2524 : (center2524.re : ℝ)^2 +
    (center2524.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2524]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2524 : work2524.theta.ok = true ∧
    work2524.jac.invOK = true ∧ acceptsUnitSq work2524.out = true := by decide +kernel

def cell2524 : CellCertificate where
  tauBall := tau2524
  contactCenter := center2524
  contactBall := contact2524
  work := work2524
  center_sq := center_sq2524
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2524.1
  jac_ok := checks2524.2.1
  accepted := checks2524.2.2

def tau2525 : RatBall :=
  ⟨⟨71/320, 97/320⟩, 3/640⟩
def center2525 : GaussianRat :=
  ⟨41431439/250000000, 204924691/1000000000⟩
def contact2525 : RatBall := localContactBall tau2525 center2525
def work2525 : RoundedTauEval :=
  evalTau precision tau2525 contact2525 logTwoBall

theorem center_sq2525 : (center2525.re : ℝ)^2 +
    (center2525.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2525]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2525 : work2525.theta.ok = true ∧
    work2525.jac.invOK = true ∧ acceptsUnitSq work2525.out = true := by decide +kernel

def cell2525 : CellCertificate where
  tauBall := tau2525
  contactCenter := center2525
  contactBall := contact2525
  work := work2525
  center_sq := center_sq2525
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2525.1
  jac_ok := checks2525.2.1
  accepted := checks2525.2.2

def tau2526 : RatBall :=
  ⟨⟨69/320, 99/320⟩, 3/640⟩
def center2526 : GaussianRat :=
  ⟨161920883/1000000000, 210031337/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0315


