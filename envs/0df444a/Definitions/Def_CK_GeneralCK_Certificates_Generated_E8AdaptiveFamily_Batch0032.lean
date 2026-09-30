-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:38:40.762016+00:00
-- url     : https://prove2.me/theorems/93d6db92-8de2-480e-a077-b140e4e5ee3c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0032.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0032_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0261 : work0261.theta.ok = true ∧
    work0261.jac.invOK = true ∧ acceptsUnitSq work0261.out = true := by decide +kernel

def cell0261 : CellCertificate where
  tauBall := tau0261
  contactCenter := center0261
  contactBall := contact0261
  work := work0261
  center_sq := center_sq0261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0261.1
  jac_ok := checks0261.2.1
  accepted := checks0261.2.2

def tau0262 : RatBall :=
  ⟨⟨-1/80, 17/80⟩, 3/160⟩
def center0262 : GaussianRat :=
  ⟨-2272549/250000000, 14963863/100000000⟩
def contact0262 : RatBall := localContactBall tau0262 center0262
def work0262 : RoundedTauEval :=
  evalTau precision tau0262 contact0262 logTwoBall

theorem center_sq0262 : (center0262.re : ℝ)^2 +
    (center0262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0262 : work0262.theta.ok = true ∧
    work0262.jac.invOK = true ∧ acceptsUnitSq work0262.out = true := by decide +kernel

def cell0262 : CellCertificate where
  tauBall := tau0262
  contactCenter := center0262
  contactBall := contact0262
  work := work0262
  center_sq := center_sq0262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0262.1
  jac_ok := checks0262.2.1
  accepted := checks0262.2.2

def tau0263 : RatBall :=
  ⟨⟨-3/80, 19/80⟩, 3/160⟩
def center0263 : GaussianRat :=
  ⟨-551859/20000000, 167686167/1000000000⟩
def contact0263 : RatBall := localContactBall tau0263 center0263
def work0263 : RoundedTauEval :=
  evalTau precision tau0263 contact0263 logTwoBall

theorem center_sq0263 : (center0263.re : ℝ)^2 +
    (center0263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0263 : work0263.theta.ok = true ∧
    work0263.jac.invOK = true ∧ acceptsUnitSq work0263.out = true := by decide +kernel

def cell0263 : CellCertificate where
  tauBall := tau0263
  contactCenter := center0263
  contactBall := contact0263
  work := work0263
  center_sq := center_sq0263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0263.1
  jac_ok := checks0263.2.1
  accepted := checks0263.2.2

def cells : List CellCertificate := [cell0256, cell0257, cell0258, cell0259, cell0260, cell0261, cell0262, cell0263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032


