-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0266_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:15:46.077158+00:00
-- url     : https://prove2.me/theorems/86280a58-48f2-4b28-b157-f5d0e7a552f6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0266 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2128 : RatBall :=
  ⟨⟨-33/320, 113/320⟩, 3/640⟩
def center2128 : GaussianRat :=
  ⟨-16312353/200000000, 252737367/1000000000⟩
def contact2128 : RatBall := localContactBall tau2128 center2128
def work2128 : RoundedTauEval :=
  evalTau precision tau2128 contact2128 logTwoBall

theorem center_sq2128 : (center2128.re : ℝ)^2 +
    (center2128.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2128]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2128 : work2128.theta.ok = true ∧
    work2128.jac.invOK = true ∧ acceptsUnitSq work2128.out = true := by decide +kernel

def cell2128 : CellCertificate where
  tauBall := tau2128
  contactCenter := center2128
  contactBall := contact2128
  work := work2128
  center_sq := center_sq2128
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2128.1
  jac_ok := checks2128.2.1
  accepted := checks2128.2.2

def tau2129 : RatBall :=
  ⟨⟨-7/64, 23/64⟩, 3/640⟩
def center2129 : GaussianRat :=
  ⟨-43440767/500000000, 257186633/1000000000⟩
def contact2129 : RatBall := localContactBall tau2129 center2129
def work2129 : RoundedTauEval :=
  evalTau precision tau2129 contact2129 logTwoBall

theorem center_sq2129 : (center2129.re : ℝ)^2 +
    (center2129.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2129]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2129 : work2129.theta.ok = true ∧
    work2129.jac.invOK = true ∧ acceptsUnitSq work2129.out = true := by decide +kernel

def cell2129 : CellCertificate where
  tauBall := tau2129
  contactCenter := center2129
  contactBall := contact2129
  work := work2129
  center_sq := center_sq2129
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2129.1
  jac_ok := checks2129.2.1
  accepted := checks2129.2.2

def tau2130 : RatBall :=
  ⟨⟨-33/320, 23/64⟩, 3/640⟩
def center2130 : GaussianRat :=
  ⟨-40992501/500000000, 257627847/1000000000⟩
def contact2130 : RatBall := localContactBall tau2130 center2130
def work2130 : RoundedTauEval :=
  evalTau precision tau2130 contact2130 logTwoBall

theorem center_sq2130 : (center2130.re : ℝ)^2 +
    (center2130.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2130]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2130 : work2130.theta.ok = true ∧
    work2130.jac.invOK = true ∧ acceptsUnitSq work2130.out = true := by decide +kernel

def cell2130 : CellCertificate where
  tauBall := tau2130
  contactCenter := center2130
  contactBall := contact2130
  work := work2130
  center_sq := center_sq2130
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2130.1
  jac_ok := checks2130.2.1
  accepted := checks2130.2.2

def tau2131 : RatBall :=
  ⟨⟨-39/320, 117/320⟩, 3/640⟩
def center2131 : GaussianRat :=
  ⟨-97144261/1000000000, 261108469/1000000000⟩
def contact2131 : RatBall := localContactBall tau2131 center2131
def work2131 : RoundedTauEval :=
  evalTau precision tau2131 contact2131 logTwoBall

theorem center_sq2131 : (center2131.re : ℝ)^2 +
    (center2131.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2131]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2131 : work2131.theta.ok = true ∧
    work2131.jac.invOK = true ∧ acceptsUnitSq work2131.out = true := by decide +kernel

def cell2131 : CellCertificate where
  tauBall := tau2131
  contactCenter := center2131
  contactBall := contact2131
  work := work2131
  center_sq := center_sq2131
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2131.1
  jac_ok := checks2131.2.1
  accepted := checks2131.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266


