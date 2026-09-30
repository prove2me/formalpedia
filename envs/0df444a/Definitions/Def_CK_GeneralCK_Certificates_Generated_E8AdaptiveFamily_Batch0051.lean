-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:50.384368+00:00
-- url     : https://prove2.me/theorems/b025778f-ddec-4986-98ba-6e5e34a1afe2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0051.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0412 : work0412.theta.ok = true ∧
    work0412.jac.invOK = true ∧ acceptsUnitSq work0412.out = true := by decide +kernel

def cell0412 : CellCertificate where
  tauBall := tau0412
  contactCenter := center0412
  contactBall := contact0412
  work := work0412
  center_sq := center_sq0412
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0412.1
  jac_ok := checks0412.2.1
  accepted := checks0412.2.2

def tau0413 : RatBall :=
  ⟨⟨-11/160, -51/160⟩, 3/320⟩
def center0413 : GaussianRat :=
  ⟨-53129867/1000000000, -56975307/250000000⟩
def contact0413 : RatBall := localContactBall tau0413 center0413
def work0413 : RoundedTauEval :=
  evalTau precision tau0413 contact0413 logTwoBall

theorem center_sq0413 : (center0413.re : ℝ)^2 +
    (center0413.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0413]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0413 : work0413.theta.ok = true ∧
    work0413.jac.invOK = true ∧ acceptsUnitSq work0413.out = true := by decide +kernel

def cell0413 : CellCertificate where
  tauBall := tau0413
  contactCenter := center0413
  contactBall := contact0413
  work := work0413
  center_sq := center_sq0413
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0413.1
  jac_ok := checks0413.2.1
  accepted := checks0413.2.2

def tau0414 : RatBall :=
  ⟨⟨-9/160, -51/160⟩, 3/320⟩
def center0414 : GaussianRat :=
  ⟨-21754011/500000000, -445983/1953125⟩
def contact0414 : RatBall := localContactBall tau0414 center0414
def work0414 : RoundedTauEval :=
  evalTau precision tau0414 contact0414 logTwoBall

theorem center_sq0414 : (center0414.re : ℝ)^2 +
    (center0414.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0414]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0414 : work0414.theta.ok = true ∧
    work0414.jac.invOK = true ∧ acceptsUnitSq work0414.out = true := by decide +kernel

def cell0414 : CellCertificate where
  tauBall := tau0414
  contactCenter := center0414
  contactBall := contact0414
  work := work0414
  center_sq := center_sq0414
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0414.1
  jac_ok := checks0414.2.1
  accepted := checks0414.2.2

def tau0415 : RatBall :=
  ⟨⟨-11/160, -49/160⟩, 3/320⟩
def center0415 : GaussianRat :=
  ⟨-52658297/1000000000, -109167283/500000000⟩
def contact0415 : RatBall := localContactBall tau0415 center0415
def work0415 : RoundedTauEval :=
  evalTau precision tau0415 contact0415 logTwoBall

theorem center_sq0415 : (center0415.re : ℝ)^2 +
    (center0415.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0415 : work0415.theta.ok = true ∧
    work0415.jac.invOK = true ∧ acceptsUnitSq work0415.out = true := by decide +kernel

def cell0415 : CellCertificate where
  tauBall := tau0415
  contactCenter := center0415
  contactBall := contact0415
  work := work0415
  center_sq := center_sq0415
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0415.1
  jac_ok := checks0415.2.1
  accepted := checks0415.2.2

def cells : List CellCertificate := [cell0408, cell0409, cell0410, cell0411, cell0412, cell0413, cell0414, cell0415]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051


