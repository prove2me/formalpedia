-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:52:38.215796+00:00
-- url     : https://prove2.me/theorems/933ee22b-74e5-421b-8c6b-320b9cf2c61a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0020.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0165 : RoundedTauEval :=
  evalTau precision tau0165 contact0165 logTwoBall

theorem center_sq0165 : (center0165.re : ℝ)^2 +
    (center0165.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0165]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0165 : work0165.theta.ok = true ∧
    work0165.jac.invOK = true ∧ acceptsUnitSq work0165.out = true := by decide +kernel

def cell0165 : CellCertificate where
  tauBall := tau0165
  contactCenter := center0165
  contactBall := contact0165
  work := work0165
  center_sq := center_sq0165
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0165.1
  jac_ok := checks0165.2.1
  accepted := checks0165.2.2

def tau0166 : RatBall :=
  ⟨⟨19/80, -11/80⟩, 3/160⟩
def center0166 : GaussianRat :=
  ⟨82225973/500000000, -18092371/200000000⟩
def contact0166 : RatBall := localContactBall tau0166 center0166
def work0166 : RoundedTauEval :=
  evalTau precision tau0166 contact0166 logTwoBall

theorem center_sq0166 : (center0166.re : ℝ)^2 +
    (center0166.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0166]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0166 : work0166.theta.ok = true ∧
    work0166.jac.invOK = true ∧ acceptsUnitSq work0166.out = true := by decide +kernel

def cell0166 : CellCertificate where
  tauBall := tau0166
  contactCenter := center0166
  contactBall := contact0166
  work := work0166
  center_sq := center_sq0166
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0166.1
  jac_ok := checks0166.2.1
  accepted := checks0166.2.2

def tau0167 : RatBall :=
  ⟨⟨17/80, -9/80⟩, 3/160⟩
def center0167 : GaussianRat :=
  ⟨29368329/200000000, -18684497/250000000⟩
def contact0167 : RatBall := localContactBall tau0167 center0167
def work0167 : RoundedTauEval :=
  evalTau precision tau0167 contact0167 logTwoBall

theorem center_sq0167 : (center0167.re : ℝ)^2 +
    (center0167.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0167]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0167 : work0167.theta.ok = true ∧
    work0167.jac.invOK = true ∧ acceptsUnitSq work0167.out = true := by decide +kernel

def cell0167 : CellCertificate where
  tauBall := tau0167
  contactCenter := center0167
  contactBall := contact0167
  work := work0167
  center_sq := center_sq0167
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0167.1
  jac_ok := checks0167.2.1
  accepted := checks0167.2.2

def cells : List CellCertificate := [cell0160, cell0161, cell0162, cell0163, cell0164, cell0165, cell0166, cell0167]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020


