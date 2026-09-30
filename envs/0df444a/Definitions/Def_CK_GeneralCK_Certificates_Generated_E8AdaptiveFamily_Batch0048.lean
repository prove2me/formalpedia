-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:51:48.383592+00:00
-- url     : https://prove2.me/theorems/6998cc68-b3f6-4a91-b7c0-b3e8fe0eba10
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0048.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0048_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0388 : (center0388.re : ℝ)^2 +
    (center0388.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0388]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0388 : work0388.theta.ok = true ∧
    work0388.jac.invOK = true ∧ acceptsUnitSq work0388.out = true := by decide +kernel

def cell0388 : CellCertificate where
  tauBall := tau0388
  contactCenter := center0388
  contactBall := contact0388
  work := work0388
  center_sq := center_sq0388
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0388.1
  jac_ok := checks0388.2.1
  accepted := checks0388.2.2

def tau0389 : RatBall :=
  ⟨⟨-7/32, -7/32⟩, 3/320⟩
def center0389 : GaussianRat :=
  ⟨-78170517/500000000, -14632387/100000000⟩
def contact0389 : RatBall := localContactBall tau0389 center0389
def work0389 : RoundedTauEval :=
  evalTau precision tau0389 contact0389 logTwoBall

theorem center_sq0389 : (center0389.re : ℝ)^2 +
    (center0389.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0389]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0389 : work0389.theta.ok = true ∧
    work0389.jac.invOK = true ∧ acceptsUnitSq work0389.out = true := by decide +kernel

def cell0389 : CellCertificate where
  tauBall := tau0389
  contactCenter := center0389
  contactBall := contact0389
  work := work0389
  center_sq := center_sq0389
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0389.1
  jac_ok := checks0389.2.1
  accepted := checks0389.2.2

def tau0390 : RatBall :=
  ⟨⟨-33/160, -7/32⟩, 3/320⟩
def center0390 : GaussianRat :=
  ⟨-7386597/50000000, -7357917/50000000⟩
def contact0390 : RatBall := localContactBall tau0390 center0390
def work0390 : RoundedTauEval :=
  evalTau precision tau0390 contact0390 logTwoBall

theorem center_sq0390 : (center0390.re : ℝ)^2 +
    (center0390.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0390]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0390 : work0390.theta.ok = true ∧
    work0390.jac.invOK = true ∧ acceptsUnitSq work0390.out = true := by decide +kernel

def cell0390 : CellCertificate where
  tauBall := tau0390
  contactCenter := center0390
  contactBall := contact0390
  work := work0390
  center_sq := center_sq0390
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0390.1
  jac_ok := checks0390.2.1
  accepted := checks0390.2.2

def tau0391 : RatBall :=
  ⟨⟨-7/32, -33/160⟩, 3/320⟩
def center0391 : GaussianRat :=
  ⟨-31103099/200000000, -137761833/1000000000⟩
def contact0391 : RatBall := localContactBall tau0391 center0391
def work0391 : RoundedTauEval :=
  evalTau precision tau0391 contact0391 logTwoBall

theorem center_sq0391 : (center0391.re : ℝ)^2 +
    (center0391.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0391]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0391 : work0391.theta.ok = true ∧
    work0391.jac.invOK = true ∧ acceptsUnitSq work0391.out = true := by decide +kernel

def cell0391 : CellCertificate where
  tauBall := tau0391
  contactCenter := center0391
  contactBall := contact0391
  work := work0391
  center_sq := center_sq0391
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0391.1
  jac_ok := checks0391.2.1
  accepted := checks0391.2.2

def cells : List CellCertificate := [cell0384, cell0385, cell0386, cell0387, cell0388, cell0389, cell0390, cell0391]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048


