-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0312_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0312_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:29:13.63044+00:00
-- url     : https://prove2.me/theorems/8d652d4b-841c-4026-a57b-4bb8df48e1c0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0312 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2496 : RatBall :=
  ⟨⟨109/320, 67/320⟩, 3/640⟩
def center2496 : GaussianRat :=
  ⟨236112247/1000000000, 65243249/500000000⟩
def contact2496 : RatBall := localContactBall tau2496 center2496
def work2496 : RoundedTauEval :=
  evalTau precision tau2496 contact2496 logTwoBall

theorem center_sq2496 : (center2496.re : ℝ)^2 +
    (center2496.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2496]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2496 : work2496.theta.ok = true ∧
    work2496.jac.invOK = true ∧ acceptsUnitSq work2496.out = true := by decide +kernel

def cell2496 : CellCertificate where
  tauBall := tau2496
  contactCenter := center2496
  contactBall := contact2496
  work := work2496
  center_sq := center_sq2496
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2496.1
  jac_ok := checks2496.2.1
  accepted := checks2496.2.2

def tau2497 : RatBall :=
  ⟨⟨21/64, 69/320⟩, 3/640⟩
def center2497 : GaussianRat :=
  ⟨57177633/250000000, 13556449/100000000⟩
def contact2497 : RatBall := localContactBall tau2497 center2497
def work2497 : RoundedTauEval :=
  evalTau precision tau2497 contact2497 logTwoBall

theorem center_sq2497 : (center2497.re : ℝ)^2 +
    (center2497.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2497]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2497 : work2497.theta.ok = true ∧
    work2497.jac.invOK = true ∧ acceptsUnitSq work2497.out = true := by decide +kernel

def cell2497 : CellCertificate where
  tauBall := tau2497
  contactCenter := center2497
  contactBall := contact2497
  work := work2497
  center_sq := center_sq2497
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2497.1
  jac_ok := checks2497.2.1
  accepted := checks2497.2.2

def tau2498 : RatBall :=
  ⟨⟨107/320, 69/320⟩, 3/640⟩
def center2498 : GaussianRat :=
  ⟨58174707/250000000, 67503627/500000000⟩
def contact2498 : RatBall := localContactBall tau2498 center2498
def work2498 : RoundedTauEval :=
  evalTau precision tau2498 contact2498 logTwoBall

theorem center_sq2498 : (center2498.re : ℝ)^2 +
    (center2498.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2498]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2498 : work2498.theta.ok = true ∧
    work2498.jac.invOK = true ∧ acceptsUnitSq work2498.out = true := by decide +kernel

def cell2498 : CellCertificate where
  tauBall := tau2498
  contactCenter := center2498
  contactBall := contact2498
  work := work2498
  center_sq := center_sq2498
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2498.1
  jac_ok := checks2498.2.1
  accepted := checks2498.2.2

def tau2499 : RatBall :=
  ⟨⟨21/64, 71/320⟩, 3/640⟩
def center2499 : GaussianRat :=
  ⟨45854809/200000000, 139564933/1000000000⟩
def contact2499 : RatBall := localContactBall tau2499 center2499
def work2499 : RoundedTauEval :=
  evalTau precision tau2499 contact2499 logTwoBall

theorem center_sq2499 : (center2499.re : ℝ)^2 +
    (center2499.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2499]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2499 : work2499.theta.ok = true ∧
    work2499.jac.invOK = true ∧ acceptsUnitSq work2499.out = true := by decide +kernel

def cell2499 : CellCertificate where
  tauBall := tau2499
  contactCenter := center2499
  contactBall := contact2499
  work := work2499
  center_sq := center_sq2499
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2499.1
  jac_ok := checks2499.2.1
  accepted := checks2499.2.2

def tau2500 : RatBall :=
  ⟨⟨107/320, 71/320⟩, 3/640⟩
def center2500 : GaussianRat :=
  ⟨58317051/250000000, 34747303/250000000⟩
def contact2500 : RatBall := localContactBall tau2500 center2500
def work2500 : RoundedTauEval :=
  evalTau precision tau2500 contact2500 logTwoBall

theorem center_sq2500 : (center2500.re : ℝ)^2 +
    (center2500.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2500 : work2500.theta.ok = true ∧
    work2500.jac.invOK = true ∧ acceptsUnitSq work2500.out = true := by decide +kernel

def cell2500 : CellCertificate where
  tauBall := tau2500
  contactCenter := center2500
  contactBall := contact2500
  work := work2500
  center_sq := center_sq2500
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2500.1
  jac_ok := checks2500.2.1
  accepted := checks2500.2.2

def tau2501 : RatBall :=
  ⟨⟨109/320, 69/320⟩, 3/640⟩
def center2501 : GaussianRat :=
  ⟨236668663/1000000000, 134444337/1000000000⟩
def contact2501 : RatBall := localContactBall tau2501 center2501
def work2501 : RoundedTauEval :=
  evalTau precision tau2501 contact2501 logTwoBall

theorem center_sq2501 : (center2501.re : ℝ)^2 +
    (center2501.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2501]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2501 : work2501.theta.ok = true ∧
    work2501.jac.invOK = true ∧ acceptsUnitSq work2501.out = true := by decide +kernel

def cell2501 : CellCertificate where
  tauBall := tau2501
  contactCenter := center2501
  contactBall := contact2501
  work := work2501
  center_sq := center_sq2501
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2501.1
  jac_ok := checks2501.2.1
  accepted := checks2501.2.2

def tau2502 : RatBall :=
  ⟨⟨101/320, 73/320⟩, 3/640⟩
def center2502 : GaussianRat :=
  ⟨44359939/200000000, 72370703/500000000⟩
def contact2502 : RatBall := localContactBall tau2502 center2502
def work2502 : RoundedTauEval :=
  evalTau precision tau2502 contact2502 logTwoBall

theorem center_sq2502 : (center2502.re : ℝ)^2 +
    (center2502.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2502]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2502 : work2502.theta.ok = true ∧
    work2502.jac.invOK = true ∧ acceptsUnitSq work2502.out = true := by decide +kernel

def cell2502 : CellCertificate where
  tauBall := tau2502
  contactCenter := center2502
  contactBall := contact2502
  work := work2502
  center_sq := center_sq2502
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2502.1
  jac_ok := checks2502.2.1
  accepted := checks2502.2.2

def tau2503 : RatBall :=
  ⟨⟨103/320, 73/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312


