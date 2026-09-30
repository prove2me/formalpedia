-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0313_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:19:18.263878+00:00
-- url     : https://prove2.me/theorems/53732acc-be9d-476d-a27e-8e2bdc9bdf8b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0313 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2504 : RatBall :=
  ⟨⟨101/320, 15/64⟩, 3/640⟩
def center2504 : GaussianRat :=
  ⟨13899213/62500000, 2975829/20000000⟩
def contact2504 : RatBall := localContactBall tau2504 center2504
def work2504 : RoundedTauEval :=
  evalTau precision tau2504 contact2504 logTwoBall

theorem center_sq2504 : (center2504.re : ℝ)^2 +
    (center2504.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2504]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2504 : work2504.theta.ok = true ∧
    work2504.jac.invOK = true ∧ acceptsUnitSq work2504.out = true := by decide +kernel

def cell2504 : CellCertificate where
  tauBall := tau2504
  contactCenter := center2504
  contactBall := contact2504
  work := work2504
  center_sq := center_sq2504
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2504.1
  jac_ok := checks2504.2.1
  accepted := checks2504.2.2

def tau2505 : RatBall :=
  ⟨⟨103/320, 15/64⟩, 3/640⟩
def center2505 : GaussianRat :=
  ⟨14151969/62500000, 148191091/1000000000⟩
def contact2505 : RatBall := localContactBall tau2505 center2505
def work2505 : RoundedTauEval :=
  evalTau precision tau2505 contact2505 logTwoBall

theorem center_sq2505 : (center2505.re : ℝ)^2 +
    (center2505.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2505]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2505 : work2505.theta.ok = true ∧
    work2505.jac.invOK = true ∧ acceptsUnitSq work2505.out = true := by decide +kernel

def cell2505 : CellCertificate where
  tauBall := tau2505
  contactCenter := center2505
  contactBall := contact2505
  work := work2505
  center_sq := center_sq2505
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2505.1
  jac_ok := checks2505.2.1
  accepted := checks2505.2.2

def tau2506 : RatBall :=
  ⟨⟨97/320, 77/320⟩, 3/640⟩
def center2506 : GaussianRat :=
  ⟨10741779/50000000, 300909/1953125⟩
def contact2506 : RatBall := localContactBall tau2506 center2506
def work2506 : RoundedTauEval :=
  evalTau precision tau2506 contact2506 logTwoBall

theorem center_sq2506 : (center2506.re : ℝ)^2 +
    (center2506.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2506]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2506 : work2506.theta.ok = true ∧
    work2506.jac.invOK = true ∧ acceptsUnitSq work2506.out = true := by decide +kernel

def cell2506 : CellCertificate where
  tauBall := tau2506
  contactCenter := center2506
  contactBall := contact2506
  work := work2506
  center_sq := center_sq2506
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2506.1
  jac_ok := checks2506.2.1
  accepted := checks2506.2.2

def tau2507 : RatBall :=
  ⟨⟨99/320, 77/320⟩, 3/640⟩
def center2507 : GaussianRat :=
  ⟨218923989/1000000000, 38365123/250000000⟩
def contact2507 : RatBall := localContactBall tau2507 center2507
def work2507 : RoundedTauEval :=
  evalTau precision tau2507 contact2507 logTwoBall

theorem center_sq2507 : (center2507.re : ℝ)^2 +
    (center2507.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2507]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2507 : work2507.theta.ok = true ∧
    work2507.jac.invOK = true ∧ acceptsUnitSq work2507.out = true := by decide +kernel

def cell2507 : CellCertificate where
  tauBall := tau2507
  contactCenter := center2507
  contactBall := contact2507
  work := work2507
  center_sq := center_sq2507
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2507.1
  jac_ok := checks2507.2.1
  accepted := checks2507.2.2

def tau2508 : RatBall :=
  ⟨⟨97/320, 79/320⟩, 3/640⟩
def center2508 : GaussianRat :=
  ⟨215446071/1000000000, 158166863/1000000000⟩
def contact2508 : RatBall := localContactBall tau2508 center2508
def work2508 : RoundedTauEval :=
  evalTau precision tau2508 contact2508 logTwoBall

theorem center_sq2508 : (center2508.re : ℝ)^2 +
    (center2508.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2508]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2508 : work2508.theta.ok = true ∧
    work2508.jac.invOK = true ∧ acceptsUnitSq work2508.out = true := by decide +kernel

def cell2508 : CellCertificate where
  tauBall := tau2508
  contactCenter := center2508
  contactBall := contact2508
  work := work2508
  center_sq := center_sq2508
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2508.1
  jac_ok := checks2508.2.1
  accepted := checks2508.2.2

def tau2509 : RatBall :=
  ⟨⟨99/320, 79/320⟩, 3/640⟩
def center2509 : GaussianRat :=
  ⟨109770971/500000000, 78771627/500000000⟩
def contact2509 : RatBall := localContactBall tau2509 center2509
def work2509 : RoundedTauEval :=
  evalTau precision tau2509 contact2509 logTwoBall

theorem center_sq2509 : (center2509.re : ℝ)^2 +
    (center2509.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2509]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313


