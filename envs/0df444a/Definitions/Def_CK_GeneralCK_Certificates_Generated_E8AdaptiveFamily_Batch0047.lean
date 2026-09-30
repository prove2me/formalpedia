-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:07.020656+00:00
-- url     : https://prove2.me/theorems/7f0d51f6-0def-4718-9cc0-0e58e257ba9c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0047.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0047_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0380 : (center0380.re : ℝ)^2 +
    (center0380.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0380]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0380 : work0380.theta.ok = true ∧
    work0380.jac.invOK = true ∧ acceptsUnitSq work0380.out = true := by decide +kernel

def cell0380 : CellCertificate where
  tauBall := tau0380
  contactCenter := center0380
  contactBall := contact0380
  work := work0380
  center_sq := center_sq0380
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0380.1
  jac_ok := checks0380.2.1
  accepted := checks0380.2.2

def tau0381 : RatBall :=
  ⟨⟨-7/32, -39/160⟩, 3/320⟩
def center0381 : GaussianRat :=
  ⟨-9885359/62500000, -81782823/500000000⟩
def contact0381 : RatBall := localContactBall tau0381 center0381
def work0381 : RoundedTauEval :=
  evalTau precision tau0381 contact0381 logTwoBall

theorem center_sq0381 : (center0381.re : ℝ)^2 +
    (center0381.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0381]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0381 : work0381.theta.ok = true ∧
    work0381.jac.invOK = true ∧ acceptsUnitSq work0381.out = true := by decide +kernel

def cell0381 : CellCertificate where
  tauBall := tau0381
  contactCenter := center0381
  contactBall := contact0381
  work := work0381
  center_sq := center_sq0381
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0381.1
  jac_ok := checks0381.2.1
  accepted := checks0381.2.2

def tau0382 : RatBall :=
  ⟨⟨-33/160, -39/160⟩, 3/320⟩
def center0382 : GaussianRat :=
  ⟨-18684153/125000000, -164515579/1000000000⟩
def contact0382 : RatBall := localContactBall tau0382 center0382
def work0382 : RoundedTauEval :=
  evalTau precision tau0382 contact0382 logTwoBall

theorem center_sq0382 : (center0382.re : ℝ)^2 +
    (center0382.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0382]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0382 : work0382.theta.ok = true ∧
    work0382.jac.invOK = true ∧ acceptsUnitSq work0382.out = true := by decide +kernel

def cell0382 : CellCertificate where
  tauBall := tau0382
  contactCenter := center0382
  contactBall := contact0382
  work := work0382
  center_sq := center_sq0382
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0382.1
  jac_ok := checks0382.2.1
  accepted := checks0382.2.2

def tau0383 : RatBall :=
  ⟨⟨-7/32, -37/160⟩, 3/320⟩
def center0383 : GaussianRat :=
  ⟨-78611951/500000000, -154924327/1000000000⟩
def contact0383 : RatBall := localContactBall tau0383 center0383
def work0383 : RoundedTauEval :=
  evalTau precision tau0383 contact0383 logTwoBall

theorem center_sq0383 : (center0383.re : ℝ)^2 +
    (center0383.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0383]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0383 : work0383.theta.ok = true ∧
    work0383.jac.invOK = true ∧ acceptsUnitSq work0383.out = true := by decide +kernel

def cell0383 : CellCertificate where
  tauBall := tau0383
  contactCenter := center0383
  contactBall := contact0383
  work := work0383
  center_sq := center_sq0383
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0383.1
  jac_ok := checks0383.2.1
  accepted := checks0383.2.2

def cells : List CellCertificate := [cell0376, cell0377, cell0378, cell0379, cell0380, cell0381, cell0382, cell0383]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047


