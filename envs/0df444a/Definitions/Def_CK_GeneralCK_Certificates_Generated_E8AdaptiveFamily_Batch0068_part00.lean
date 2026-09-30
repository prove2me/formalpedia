-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:07:19.312075+00:00
-- url     : https://prove2.me/theorems/06520128-9165-4e82-a052-ea13b5b500c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0068 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0544 : RatBall :=
  ⟨⟨-63/160, -13/160⟩, 3/320⟩
def center0544 : GaussianRat :=
  ⟨-260916819/1000000000, -48524207/1000000000⟩
def contact0544 : RatBall := localContactBall tau0544 center0544
def work0544 : RoundedTauEval :=
  evalTau precision tau0544 contact0544 logTwoBall

theorem center_sq0544 : (center0544.re : ℝ)^2 +
    (center0544.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0544]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0544 : work0544.theta.ok = true ∧
    work0544.jac.invOK = true ∧ acceptsUnitSq work0544.out = true := by decide +kernel

def cell0544 : CellCertificate where
  tauBall := tau0544
  contactCenter := center0544
  contactBall := contact0544
  work := work0544
  center_sq := center_sq0544
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0544.1
  jac_ok := checks0544.2.1
  accepted := checks0544.2.2

def tau0545 : RatBall :=
  ⟨⟨-61/160, -13/160⟩, 3/320⟩
def center0545 : GaussianRat :=
  ⟨-126702243/500000000, -6119291/125000000⟩
def contact0545 : RatBall := localContactBall tau0545 center0545
def work0545 : RoundedTauEval :=
  evalTau precision tau0545 contact0545 logTwoBall

theorem center_sq0545 : (center0545.re : ℝ)^2 +
    (center0545.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0545]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0545 : work0545.theta.ok = true ∧
    work0545.jac.invOK = true ∧ acceptsUnitSq work0545.out = true := by decide +kernel

def cell0545 : CellCertificate where
  tauBall := tau0545
  contactCenter := center0545
  contactBall := contact0545
  work := work0545
  center_sq := center_sq0545
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0545.1
  jac_ok := checks0545.2.1
  accepted := checks0545.2.2

def tau0546 : RatBall :=
  ⟨⟨-59/160, -3/32⟩, 3/320⟩
def center0546 : GaussianRat :=
  ⟨-246278271/1000000000, -56993771/1000000000⟩
def contact0546 : RatBall := localContactBall tau0546 center0546
def work0546 : RoundedTauEval :=
  evalTau precision tau0546 contact0546 logTwoBall

theorem center_sq0546 : (center0546.re : ℝ)^2 +
    (center0546.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0546]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0546 : work0546.theta.ok = true ∧
    work0546.jac.invOK = true ∧ acceptsUnitSq work0546.out = true := by decide +kernel

def cell0546 : CellCertificate where
  tauBall := tau0546
  contactCenter := center0546
  contactBall := contact0546
  work := work0546
  center_sq := center_sq0546
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0546.1
  jac_ok := checks0546.2.1
  accepted := checks0546.2.2

def tau0547 : RatBall :=
  ⟨⟨-57/160, -3/32⟩, 3/320⟩
def center0547 : GaussianRat :=
  ⟨-11931267/50000000, -14368881/250000000⟩
def contact0547 : RatBall := localContactBall tau0547 center0547
def work0547 : RoundedTauEval :=
  evalTau precision tau0547 contact0547 logTwoBall

theorem center_sq0547 : (center0547.re : ℝ)^2 +
    (center0547.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0547]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0547 : work0547.theta.ok = true ∧
    work0547.jac.invOK = true ∧ acceptsUnitSq work0547.out = true := by decide +kernel

def cell0547 : CellCertificate where
  tauBall := tau0547
  contactCenter := center0547
  contactBall := contact0547
  work := work0547
  center_sq := center_sq0547
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0547.1
  jac_ok := checks0547.2.1
  accepted := checks0547.2.2

def tau0548 : RatBall :=
  ⟨⟨-59/160, -13/160⟩, 3/320⟩
def center0548 : GaussianRat :=
  ⟨-245825343/1000000000, -12344447/250000000⟩
def contact0548 : RatBall := localContactBall tau0548 center0548
def work0548 : RoundedTauEval :=
  evalTau precision tau0548 contact0548 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068


