-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:00:45.0263+00:00
-- url     : https://prove2.me/theorems/c9123001-4024-4580-ab86-b0eaa7625022
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0097 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0097_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0780 : RatBall :=
  ⟨⟨-63/160, 13/160⟩, 3/320⟩
def center0780 : GaussianRat :=
  ⟨-260916819/1000000000, 48524207/1000000000⟩
def contact0780 : RatBall := localContactBall tau0780 center0780
def work0780 : RoundedTauEval :=
  evalTau precision tau0780 contact0780 logTwoBall

theorem center_sq0780 : (center0780.re : ℝ)^2 +
    (center0780.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0780]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0780 : work0780.theta.ok = true ∧
    work0780.jac.invOK = true ∧ acceptsUnitSq work0780.out = true := by decide +kernel

def cell0780 : CellCertificate where
  tauBall := tau0780
  contactCenter := center0780
  contactBall := contact0780
  work := work0780
  center_sq := center_sq0780
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0780.1
  jac_ok := checks0780.2.1
  accepted := checks0780.2.2

def tau0781 : RatBall :=
  ⟨⟨-61/160, 13/160⟩, 3/320⟩
def center0781 : GaussianRat :=
  ⟨-126702243/500000000, 6119291/125000000⟩
def contact0781 : RatBall := localContactBall tau0781 center0781
def work0781 : RoundedTauEval :=
  evalTau precision tau0781 contact0781 logTwoBall

theorem center_sq0781 : (center0781.re : ℝ)^2 +
    (center0781.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0781]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0781 : work0781.theta.ok = true ∧
    work0781.jac.invOK = true ∧ acceptsUnitSq work0781.out = true := by decide +kernel

def cell0781 : CellCertificate where
  tauBall := tau0781
  contactCenter := center0781
  contactBall := contact0781
  work := work0781
  center_sq := center_sq0781
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0781.1
  jac_ok := checks0781.2.1
  accepted := checks0781.2.2

def tau0782 : RatBall :=
  ⟨⟨-63/160, 3/32⟩, 3/320⟩
def center0782 : GaussianRat :=
  ⟨-65346019/250000000, 28003013/500000000⟩
def contact0782 : RatBall := localContactBall tau0782 center0782
def work0782 : RoundedTauEval :=
  evalTau precision tau0782 contact0782 logTwoBall

theorem center_sq0782 : (center0782.re : ℝ)^2 +
    (center0782.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0782]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0782 : work0782.theta.ok = true ∧
    work0782.jac.invOK = true ∧ acceptsUnitSq work0782.out = true := by decide +kernel

def cell0782 : CellCertificate where
  tauBall := tau0782
  contactCenter := center0782
  contactBall := contact0782
  work := work0782
  center_sq := center_sq0782
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0782.1
  jac_ok := checks0782.2.1
  accepted := checks0782.2.2

def tau0783 : RatBall :=
  ⟨⟨-61/160, 3/32⟩, 3/320⟩
def center0783 : GaussianRat :=
  ⟨-50772973/200000000, 14125933/250000000⟩
def contact0783 : RatBall := localContactBall tau0783 center0783
def work0783 : RoundedTauEval :=
  evalTau precision tau0783 contact0783 logTwoBall

theorem center_sq0783 : (center0783.re : ℝ)^2 +
    (center0783.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0783]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0783 : work0783.theta.ok = true ∧
    work0783.jac.invOK = true ∧ acceptsUnitSq work0783.out = true := by decide +kernel

def cell0783 : CellCertificate where
  tauBall := tau0783
  contactCenter := center0783
  contactBall := contact0783
  work := work0783
  center_sq := center_sq0783
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0783.1
  jac_ok := checks0783.2.1
  accepted := checks0783.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097


