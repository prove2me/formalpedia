-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0013
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0013
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:33:22.560869+00:00
-- url     : https://prove2.me/theorems/ed95d334-202f-4b8a-88ff-ffe5be7b69f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0013.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0013_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0108 : (center0108.re : ℝ)^2 +
    (center0108.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0108]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0108 : work0108.theta.ok = true ∧
    work0108.jac.invOK = true ∧ acceptsUnitSq work0108.out = true := by decide +kernel

def cell0108 : CellCertificate where
  tauBall := tau0108
  contactCenter := center0108
  contactBall := contact0108
  work := work0108
  center_sq := center_sq0108
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0108.1
  jac_ok := checks0108.2.1
  accepted := checks0108.2.2

def tau0109 : RatBall :=
  ⟨⟨-3/16, -3/16⟩, 3/160⟩
def center0109 : GaussianRat :=
  ⟨-132989007/1000000000, -15833617/125000000⟩
def contact0109 : RatBall := localContactBall tau0109 center0109
def work0109 : RoundedTauEval :=
  evalTau precision tau0109 contact0109 logTwoBall

theorem center_sq0109 : (center0109.re : ℝ)^2 +
    (center0109.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0109]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0109 : work0109.theta.ok = true ∧
    work0109.jac.invOK = true ∧ acceptsUnitSq work0109.out = true := by decide +kernel

def cell0109 : CellCertificate where
  tauBall := tau0109
  contactCenter := center0109
  contactBall := contact0109
  work := work0109
  center_sq := center_sq0109
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0109.1
  jac_ok := checks0109.2.1
  accepted := checks0109.2.2

def tau0110 : RatBall :=
  ⟨⟨-13/80, -3/16⟩, 3/160⟩
def center0110 : GaussianRat :=
  ⟨-115659239/1000000000, -127856533/1000000000⟩
def contact0110 : RatBall := localContactBall tau0110 center0110
def work0110 : RoundedTauEval :=
  evalTau precision tau0110 contact0110 logTwoBall

theorem center_sq0110 : (center0110.re : ℝ)^2 +
    (center0110.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0110]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0110 : work0110.theta.ok = true ∧
    work0110.jac.invOK = true ∧ acceptsUnitSq work0110.out = true := by decide +kernel

def cell0110 : CellCertificate where
  tauBall := tau0110
  contactCenter := center0110
  contactBall := contact0110
  work := work0110
  center_sq := center_sq0110
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0110.1
  jac_ok := checks0110.2.1
  accepted := checks0110.2.2

def tau0111 : RatBall :=
  ⟨⟨-3/16, -13/80⟩, 3/160⟩
def center0111 : GaussianRat :=
  ⟨-131822371/1000000000, -13687313/125000000⟩
def contact0111 : RatBall := localContactBall tau0111 center0111
def work0111 : RoundedTauEval :=
  evalTau precision tau0111 contact0111 logTwoBall

theorem center_sq0111 : (center0111.re : ℝ)^2 +
    (center0111.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0111 : work0111.theta.ok = true ∧
    work0111.jac.invOK = true ∧ acceptsUnitSq work0111.out = true := by decide +kernel

def cell0111 : CellCertificate where
  tauBall := tau0111
  contactCenter := center0111
  contactBall := contact0111
  work := work0111
  center_sq := center_sq0111
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0111.1
  jac_ok := checks0111.2.1
  accepted := checks0111.2.2

def cells : List CellCertificate := [cell0104, cell0105, cell0106, cell0107, cell0108, cell0109, cell0110, cell0111]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013


