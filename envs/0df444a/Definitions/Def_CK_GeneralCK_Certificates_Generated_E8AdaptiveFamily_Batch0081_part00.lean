-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0081_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:17:02.390424+00:00
-- url     : https://prove2.me/theorems/aebb7d0b-4c95-499c-b518-4e8601ccdbde
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0081 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0648 : RatBall :=
  ⟨⟨33/160, -43/160⟩, 3/320⟩
def center0648 : GaussianRat :=
  ⟨151447357/1000000000, -91026767/500000000⟩
def contact0648 : RatBall := localContactBall tau0648 center0648
def work0648 : RoundedTauEval :=
  evalTau precision tau0648 contact0648 logTwoBall

theorem center_sq0648 : (center0648.re : ℝ)^2 +
    (center0648.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0648]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0648 : work0648.theta.ok = true ∧
    work0648.jac.invOK = true ∧ acceptsUnitSq work0648.out = true := by decide +kernel

def cell0648 : CellCertificate where
  tauBall := tau0648
  contactCenter := center0648
  contactBall := contact0648
  work := work0648
  center_sq := center_sq0648
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0648.1
  jac_ok := checks0648.2.1
  accepted := checks0648.2.2

def tau0649 : RatBall :=
  ⟨⟨7/32, -43/160⟩, 3/320⟩
def center0649 : GaussianRat :=
  ⟨160233593/1000000000, -180980837/1000000000⟩
def contact0649 : RatBall := localContactBall tau0649 center0649
def work0649 : RoundedTauEval :=
  evalTau precision tau0649 contact0649 logTwoBall

theorem center_sq0649 : (center0649.re : ℝ)^2 +
    (center0649.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0649]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0649 : work0649.theta.ok = true ∧
    work0649.jac.invOK = true ∧ acceptsUnitSq work0649.out = true := by decide +kernel

def cell0649 : CellCertificate where
  tauBall := tau0649
  contactCenter := center0649
  contactBall := contact0649
  work := work0649
  center_sq := center_sq0649
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0649.1
  jac_ok := checks0649.2.1
  accepted := checks0649.2.2

def tau0650 : RatBall :=
  ⟨⟨33/160, -41/160⟩, 3/320⟩
def center0650 : GaussianRat :=
  ⟨150430267/1000000000, -1082879/6250000⟩
def contact0650 : RatBall := localContactBall tau0650 center0650
def work0650 : RoundedTauEval :=
  evalTau precision tau0650 contact0650 logTwoBall

theorem center_sq0650 : (center0650.re : ℝ)^2 +
    (center0650.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0650]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0650 : work0650.theta.ok = true ∧
    work0650.jac.invOK = true ∧ acceptsUnitSq work0650.out = true := by decide +kernel

def cell0650 : CellCertificate where
  tauBall := tau0650
  contactCenter := center0650
  contactBall := contact0650
  work := work0650
  center_sq := center_sq0650
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0650.1
  jac_ok := checks0650.2.1
  accepted := checks0650.2.2

def tau0651 : RatBall :=
  ⟨⟨7/32, -41/160⟩, 3/320⟩
def center0651 : GaussianRat :=
  ⟨31833667/200000000, -43062577/250000000⟩
def contact0651 : RatBall := localContactBall tau0651 center0651
def work0651 : RoundedTauEval :=
  evalTau precision tau0651 contact0651 logTwoBall

theorem center_sq0651 : (center0651.re : ℝ)^2 +
    (center0651.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0651]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0651 : work0651.theta.ok = true ∧
    work0651.jac.invOK = true ∧ acceptsUnitSq work0651.out = true := by decide +kernel

def cell0651 : CellCertificate where
  tauBall := tau0651
  contactCenter := center0651
  contactBall := contact0651
  work := work0651
  center_sq := center_sq0651
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0651.1
  jac_ok := checks0651.2.1
  accepted := checks0651.2.2

def tau0652 : RatBall :=
  ⟨⟨37/160, -43/160⟩, 3/320⟩
def center0652 : GaussianRat :=
  ⟨84477561/500000000, -89929857/500000000⟩
def contact0652 : RatBall := localContactBall tau0652 center0652
def work0652 : RoundedTauEval :=
  evalTau precision tau0652 contact0652 logTwoBall

theorem center_sq0652 : (center0652.re : ℝ)^2 +
    (center0652.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0652]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0652 : work0652.theta.ok = true ∧
    work0652.jac.invOK = true ∧ acceptsUnitSq work0652.out = true := by decide +kernel

def cell0652 : CellCertificate where
  tauBall := tau0652
  contactCenter := center0652
  contactBall := contact0652
  work := work0652
  center_sq := center_sq0652
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0652.1
  jac_ok := checks0652.2.1
  accepted := checks0652.2.2

def tau0653 : RatBall :=
  ⟨⟨39/160, -43/160⟩, 3/320⟩
def center0653 : GaussianRat :=
  ⟨177609433/1000000000, -178692329/1000000000⟩
def contact0653 : RatBall := localContactBall tau0653 center0653
def work0653 : RoundedTauEval :=
  evalTau precision tau0653 contact0653 logTwoBall

theorem center_sq0653 : (center0653.re : ℝ)^2 +
    (center0653.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0653]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0653 : work0653.theta.ok = true ∧
    work0653.jac.invOK = true ∧ acceptsUnitSq work0653.out = true := by decide +kernel

def cell0653 : CellCertificate where
  tauBall := tau0653
  contactCenter := center0653
  contactBall := contact0653
  work := work0653
  center_sq := center_sq0653
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0653.1
  jac_ok := checks0653.2.1
  accepted := checks0653.2.2

def tau0654 : RatBall :=
  ⟨⟨37/160, -41/160⟩, 3/320⟩
def center0654 : GaussianRat :=
  ⟨167843761/1000000000, -171194117/1000000000⟩
def contact0654 : RatBall := localContactBall tau0654 center0654
def work0654 : RoundedTauEval :=
  evalTau precision tau0654 contact0654 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081


