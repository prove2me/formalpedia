-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:29:15.969598+00:00
-- url     : https://prove2.me/theorems/1ca06234-81c5-4718-b6ab-237f32bf21cf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0035.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0035_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0284 : work0284.theta.ok = true ∧
    work0284.jac.invOK = true ∧ acceptsUnitSq work0284.out = true := by decide +kernel

def cell0284 : CellCertificate where
  tauBall := tau0284
  contactCenter := center0284
  contactBall := contact0284
  work := work0284
  center_sq := center_sq0284
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0284.1
  jac_ok := checks0284.2.1
  accepted := checks0284.2.2

def tau0285 : RatBall :=
  ⟨⟨13/80, 3/16⟩, 3/160⟩
def center0285 : GaussianRat :=
  ⟨115659239/1000000000, 127856533/1000000000⟩
def contact0285 : RatBall := localContactBall tau0285 center0285
def work0285 : RoundedTauEval :=
  evalTau precision tau0285 contact0285 logTwoBall

theorem center_sq0285 : (center0285.re : ℝ)^2 +
    (center0285.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0285]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0285 : work0285.theta.ok = true ∧
    work0285.jac.invOK = true ∧ acceptsUnitSq work0285.out = true := by decide +kernel

def cell0285 : CellCertificate where
  tauBall := tau0285
  contactCenter := center0285
  contactBall := contact0285
  work := work0285
  center_sq := center_sq0285
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0285.1
  jac_ok := checks0285.2.1
  accepted := checks0285.2.2

def tau0286 : RatBall :=
  ⟨⟨3/16, 3/16⟩, 3/160⟩
def center0286 : GaussianRat :=
  ⟨132989007/1000000000, 15833617/125000000⟩
def contact0286 : RatBall := localContactBall tau0286 center0286
def work0286 : RoundedTauEval :=
  evalTau precision tau0286 contact0286 logTwoBall

theorem center_sq0286 : (center0286.re : ℝ)^2 +
    (center0286.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0286]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0286 : work0286.theta.ok = true ∧
    work0286.jac.invOK = true ∧ acceptsUnitSq work0286.out = true := by decide +kernel

def cell0286 : CellCertificate where
  tauBall := tau0286
  contactCenter := center0286
  contactBall := contact0286
  work := work0286
  center_sq := center_sq0286
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0286.1
  jac_ok := checks0286.2.1
  accepted := checks0286.2.2

def tau0287 : RatBall :=
  ⟨⟨21/80, 1/80⟩, 3/160⟩
def center0287 : GaussianRat :=
  ⟨4445163/25000000, 8084719/1000000000⟩
def contact0287 : RatBall := localContactBall tau0287 center0287
def work0287 : RoundedTauEval :=
  evalTau precision tau0287 contact0287 logTwoBall

theorem center_sq0287 : (center0287.re : ℝ)^2 +
    (center0287.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0287]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0287 : work0287.theta.ok = true ∧
    work0287.jac.invOK = true ∧ acceptsUnitSq work0287.out = true := by decide +kernel

def cell0287 : CellCertificate where
  tauBall := tau0287
  contactCenter := center0287
  contactBall := contact0287
  work := work0287
  center_sq := center_sq0287
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0287.1
  jac_ok := checks0287.2.1
  accepted := checks0287.2.2

def cells : List CellCertificate := [cell0280, cell0281, cell0282, cell0283, cell0284, cell0285, cell0286, cell0287]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035


