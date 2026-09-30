-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:53:43.510827+00:00
-- url     : https://prove2.me/theorems/a819fe7d-6e20-4339-8597-accff3c39772
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0046.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0046_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0372 : CellCertificate where
  tauBall := tau0372
  contactCenter := center0372
  contactBall := contact0372
  work := work0372
  center_sq := center_sq0372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0372.1
  jac_ok := checks0372.2.1
  accepted := checks0372.2.2

def tau0373 : RatBall :=
  ⟨⟨-43/160, -7/32⟩, 3/320⟩
def center0373 : GaussianRat :=
  ⟨-9509069/50000000, -71308977/500000000⟩
def contact0373 : RatBall := localContactBall tau0373 center0373
def work0373 : RoundedTauEval :=
  evalTau precision tau0373 contact0373 logTwoBall

theorem center_sq0373 : (center0373.re : ℝ)^2 +
    (center0373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0373 : work0373.theta.ok = true ∧
    work0373.jac.invOK = true ∧ acceptsUnitSq work0373.out = true := by decide +kernel

def cell0373 : CellCertificate where
  tauBall := tau0373
  contactCenter := center0373
  contactBall := contact0373
  work := work0373
  center_sq := center_sq0373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0373.1
  jac_ok := checks0373.2.1
  accepted := checks0373.2.2

def tau0374 : RatBall :=
  ⟨⟨-41/160, -7/32⟩, 3/320⟩
def center0374 : GaussianRat :=
  ⟨-90907579/500000000, -143596387/1000000000⟩
def contact0374 : RatBall := localContactBall tau0374 center0374
def work0374 : RoundedTauEval :=
  evalTau precision tau0374 contact0374 logTwoBall

theorem center_sq0374 : (center0374.re : ℝ)^2 +
    (center0374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0374 : work0374.theta.ok = true ∧
    work0374.jac.invOK = true ∧ acceptsUnitSq work0374.out = true := by decide +kernel

def cell0374 : CellCertificate where
  tauBall := tau0374
  contactCenter := center0374
  contactBall := contact0374
  work := work0374
  center_sq := center_sq0374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0374.1
  jac_ok := checks0374.2.1
  accepted := checks0374.2.2

def tau0375 : RatBall :=
  ⟨⟨-43/160, -33/160⟩, 3/320⟩
def center0375 : GaussianRat :=
  ⟨-189219451/1000000000, -67150009/500000000⟩
def contact0375 : RatBall := localContactBall tau0375 center0375
def work0375 : RoundedTauEval :=
  evalTau precision tau0375 contact0375 logTwoBall

theorem center_sq0375 : (center0375.re : ℝ)^2 +
    (center0375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0375 : work0375.theta.ok = true ∧
    work0375.jac.invOK = true ∧ acceptsUnitSq work0375.out = true := by decide +kernel

def cell0375 : CellCertificate where
  tauBall := tau0375
  contactCenter := center0375
  contactBall := contact0375
  work := work0375
  center_sq := center_sq0375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0375.1
  jac_ok := checks0375.2.1
  accepted := checks0375.2.2

def cells : List CellCertificate := [cell0368, cell0369, cell0370, cell0371, cell0372, cell0373, cell0374, cell0375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046


