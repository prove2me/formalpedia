-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:46:50.68914+00:00
-- url     : https://prove2.me/theorems/42893ee6-b8a1-4b01-88c3-3dbb2d037990
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0068.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0068_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0548 : (center0548.re : ℝ)^2 +
    (center0548.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0548]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0548 : work0548.theta.ok = true ∧
    work0548.jac.invOK = true ∧ acceptsUnitSq work0548.out = true := by decide +kernel

def cell0548 : CellCertificate where
  tauBall := tau0548
  contactCenter := center0548
  contactBall := contact0548
  work := work0548
  center_sq := center_sq0548
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0548.1
  jac_ok := checks0548.2.1
  accepted := checks0548.2.2

def tau0549 : RatBall :=
  ⟨⟨-57/160, -13/160⟩, 3/320⟩
def center0549 : GaussianRat :=
  ⟨-238180443/1000000000, -24897027/500000000⟩
def contact0549 : RatBall := localContactBall tau0549 center0549
def work0549 : RoundedTauEval :=
  evalTau precision tau0549 contact0549 logTwoBall

theorem center_sq0549 : (center0549.re : ℝ)^2 +
    (center0549.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0549]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0549 : work0549.theta.ok = true ∧
    work0549.jac.invOK = true ∧ acceptsUnitSq work0549.out = true := by decide +kernel

def cell0549 : CellCertificate where
  tauBall := tau0549
  contactCenter := center0549
  contactBall := contact0549
  work := work0549
  center_sq := center_sq0549
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0549.1
  jac_ok := checks0549.2.1
  accepted := checks0549.2.2

def tau0550 : RatBall :=
  ⟨⟨-63/160, -11/160⟩, 3/320⟩
def center0550 : GaussianRat :=
  ⟨-260517353/1000000000, -1026213/25000000⟩
def contact0550 : RatBall := localContactBall tau0550 center0550
def work0550 : RoundedTauEval :=
  evalTau precision tau0550 contact0550 logTwoBall

theorem center_sq0550 : (center0550.re : ℝ)^2 +
    (center0550.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0550]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0550 : work0550.theta.ok = true ∧
    work0550.jac.invOK = true ∧ acceptsUnitSq work0550.out = true := by decide +kernel

def cell0550 : CellCertificate where
  tauBall := tau0550
  contactCenter := center0550
  contactBall := contact0550
  work := work0550
  center_sq := center_sq0550
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0550.1
  jac_ok := checks0550.2.1
  accepted := checks0550.2.2

def tau0551 : RatBall :=
  ⟨⟨-61/160, -11/160⟩, 3/320⟩
def center0551 : GaussianRat :=
  ⟨-25301093/100000000, -41411583/1000000000⟩
def contact0551 : RatBall := localContactBall tau0551 center0551
def work0551 : RoundedTauEval :=
  evalTau precision tau0551 contact0551 logTwoBall

theorem center_sq0551 : (center0551.re : ℝ)^2 +
    (center0551.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0551]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0551 : work0551.theta.ok = true ∧
    work0551.jac.invOK = true ∧ acceptsUnitSq work0551.out = true := by decide +kernel

def cell0551 : CellCertificate where
  tauBall := tau0551
  contactCenter := center0551
  contactBall := contact0551
  work := work0551
  center_sq := center_sq0551
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0551.1
  jac_ok := checks0551.2.1
  accepted := checks0551.2.2

def cells : List CellCertificate := [cell0544, cell0545, cell0546, cell0547, cell0548, cell0549, cell0550, cell0551]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068


