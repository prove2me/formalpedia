-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:36:49.594987+00:00
-- url     : https://prove2.me/theorems/c2136686-f5fd-4cea-b1de-aa52598dd5aa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0118 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0118_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0948 : RatBall :=
  ⟨⟨-23/160, 49/160⟩, 3/320⟩
def center0948 : GaussianRat :=
  ⟨-109172181/1000000000, 42835301/200000000⟩
def contact0948 : RatBall := localContactBall tau0948 center0948
def work0948 : RoundedTauEval :=
  evalTau precision tau0948 contact0948 logTwoBall

theorem center_sq0948 : (center0948.re : ℝ)^2 +
    (center0948.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0948]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0948 : work0948.theta.ok = true ∧
    work0948.jac.invOK = true ∧ acceptsUnitSq work0948.out = true := by decide +kernel

def cell0948 : CellCertificate where
  tauBall := tau0948
  contactCenter := center0948
  contactBall := contact0948
  work := work0948
  center_sq := center_sq0948
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0948.1
  jac_ok := checks0948.2.1
  accepted := checks0948.2.2

def tau0949 : RatBall :=
  ⟨⟨-21/160, 49/160⟩, 3/320⟩
def center0949 : GaussianRat :=
  ⟨-9985979/100000000, 43011679/200000000⟩
def contact0949 : RatBall := localContactBall tau0949 center0949
def work0949 : RoundedTauEval :=
  evalTau precision tau0949 contact0949 logTwoBall

theorem center_sq0949 : (center0949.re : ℝ)^2 +
    (center0949.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0949]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0949 : work0949.theta.ok = true ∧
    work0949.jac.invOK = true ∧ acceptsUnitSq work0949.out = true := by decide +kernel

def cell0949 : CellCertificate where
  tauBall := tau0949
  contactCenter := center0949
  contactBall := contact0949
  work := work0949
  center_sq := center_sq0949
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0949.1
  jac_ok := checks0949.2.1
  accepted := checks0949.2.2

def tau0950 : RatBall :=
  ⟨⟨-21/160, 51/160⟩, 3/320⟩
def center0950 : GaussianRat :=
  ⟨-100729897/1000000000, 44886561/200000000⟩
def contact0950 : RatBall := localContactBall tau0950 center0950
def work0950 : RoundedTauEval :=
  evalTau precision tau0950 contact0950 logTwoBall

theorem center_sq0950 : (center0950.re : ℝ)^2 +
    (center0950.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0950]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0950 : work0950.theta.ok = true ∧
    work0950.jac.invOK = true ∧ acceptsUnitSq work0950.out = true := by decide +kernel

def cell0950 : CellCertificate where
  tauBall := tau0950
  contactCenter := center0950
  contactBall := contact0950
  work := work0950
  center_sq := center_sq0950
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0950.1
  jac_ok := checks0950.2.1
  accepted := checks0950.2.2

def tau0951 : RatBall :=
  ⟨⟨-19/160, 49/160⟩, 3/320⟩
def center0951 : GaussianRat :=
  ⟨-90499187/1000000000, 215867147/1000000000⟩
def contact0951 : RatBall := localContactBall tau0951 center0951
def work0951 : RoundedTauEval :=
  evalTau precision tau0951 contact0951 logTwoBall

theorem center_sq0951 : (center0951.re : ℝ)^2 +
    (center0951.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0951]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0951 : work0951.theta.ok = true ∧
    work0951.jac.invOK = true ∧ acceptsUnitSq work0951.out = true := by decide +kernel

def cell0951 : CellCertificate where
  tauBall := tau0951
  contactCenter := center0951
  contactBall := contact0951
  work := work0951
  center_sq := center_sq0951
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0951.1
  jac_ok := checks0951.2.1
  accepted := checks0951.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118


