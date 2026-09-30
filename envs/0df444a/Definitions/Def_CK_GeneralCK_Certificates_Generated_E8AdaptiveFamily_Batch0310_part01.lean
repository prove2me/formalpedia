-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:10:30.459227+00:00
-- url     : https://prove2.me/theorems/ff6620a9-9e89-4014-91ec-5fd10fee1d51
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0310 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0310_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2484 : RatBall :=
  ⟨⟨17/64, 93/320⟩, 3/640⟩
def center2484 : GaussianRat :=
  ⟨97455589/500000000, 191473909/1000000000⟩
def contact2484 : RatBall := localContactBall tau2484 center2484
def work2484 : RoundedTauEval :=
  evalTau precision tau2484 contact2484 logTwoBall

theorem center_sq2484 : (center2484.re : ℝ)^2 +
    (center2484.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2484]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2484 : work2484.theta.ok = true ∧
    work2484.jac.invOK = true ∧ acceptsUnitSq work2484.out = true := by decide +kernel

def cell2484 : CellCertificate where
  tauBall := tau2484
  contactCenter := center2484
  contactBall := contact2484
  work := work2484
  center_sq := center_sq2484
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2484.1
  jac_ok := checks2484.2.1
  accepted := checks2484.2.2

def tau2485 : RatBall :=
  ⟨⟨87/320, 93/320⟩, 3/640⟩
def center2485 : GaussianRat :=
  ⟨2489819/12500000, 47692707/250000000⟩
def contact2485 : RatBall := localContactBall tau2485 center2485
def work2485 : RoundedTauEval :=
  evalTau precision tau2485 contact2485 logTwoBall

theorem center_sq2485 : (center2485.re : ℝ)^2 +
    (center2485.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2485]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2485 : work2485.theta.ok = true ∧
    work2485.jac.invOK = true ∧ acceptsUnitSq work2485.out = true := by decide +kernel

def cell2485 : CellCertificate where
  tauBall := tau2485
  contactCenter := center2485
  contactBall := contact2485
  work := work2485
  center_sq := center_sq2485
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2485.1
  jac_ok := checks2485.2.1
  accepted := checks2485.2.2

def tau2486 : RatBall :=
  ⟨⟨17/64, 19/64⟩, 3/640⟩
def center2486 : GaussianRat :=
  ⟨39123719/200000000, 48940869/250000000⟩
def contact2486 : RatBall := localContactBall tau2486 center2486
def work2486 : RoundedTauEval :=
  evalTau precision tau2486 contact2486 logTwoBall

theorem center_sq2486 : (center2486.re : ℝ)^2 +
    (center2486.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2486]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2486 : work2486.theta.ok = true ∧
    work2486.jac.invOK = true ∧ acceptsUnitSq work2486.out = true := by decide +kernel

def cell2486 : CellCertificate where
  tauBall := tau2486
  contactCenter := center2486
  contactBall := contact2486
  work := work2486
  center_sq := center_sq2486
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2486.1
  jac_ok := checks2486.2.1
  accepted := checks2486.2.2

def tau2487 : RatBall :=
  ⟨⟨87/320, 19/64⟩, 3/640⟩
def center2487 : GaussianRat :=
  ⟨199903813/1000000000, 195040739/1000000000⟩
def contact2487 : RatBall := localContactBall tau2487 center2487
def work2487 : RoundedTauEval :=
  evalTau precision tau2487 contact2487 logTwoBall

theorem center_sq2487 : (center2487.re : ℝ)^2 +
    (center2487.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2487]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2487 : work2487.theta.ok = true ∧
    work2487.jac.invOK = true ∧ acceptsUnitSq work2487.out = true := by decide +kernel

def cell2487 : CellCertificate where
  tauBall := tau2487
  contactCenter := center2487
  contactBall := contact2487
  work := work2487
  center_sq := center_sq2487
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2487.1
  jac_ok := checks2487.2.1
  accepted := checks2487.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310


