-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:06:33.447118+00:00
-- url     : https://prove2.me/theorems/310bc53a-0383-4704-8389-0642e5a9c488
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0069.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0069_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work0557 : RoundedTauEval :=
  evalTau precision tau0557 contact0557 logTwoBall

theorem center_sq0557 : (center0557.re : ℝ)^2 +
    (center0557.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0557]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0557 : work0557.theta.ok = true ∧
    work0557.jac.invOK = true ∧ acceptsUnitSq work0557.out = true := by decide +kernel

def cell0557 : CellCertificate where
  tauBall := tau0557
  contactCenter := center0557
  contactBall := contact0557
  work := work0557
  center_sq := center_sq0557
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0557.1
  jac_ok := checks0557.2.1
  accepted := checks0557.2.2

def tau0558 : RatBall :=
  ⟨⟨1/160, -57/160⟩, 3/320⟩
def center0558 : GaussianRat :=
  ⟨311809/62500000, -5174291/20000000⟩
def contact0558 : RatBall := localContactBall tau0558 center0558
def work0558 : RoundedTauEval :=
  evalTau precision tau0558 contact0558 logTwoBall

theorem center_sq0558 : (center0558.re : ℝ)^2 +
    (center0558.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0558]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0558 : work0558.theta.ok = true ∧
    work0558.jac.invOK = true ∧ acceptsUnitSq work0558.out = true := by decide +kernel

def cell0558 : CellCertificate where
  tauBall := tau0558
  contactCenter := center0558
  contactBall := contact0558
  work := work0558
  center_sq := center_sq0558
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0558.1
  jac_ok := checks0558.2.1
  accepted := checks0558.2.2

def tau0559 : RatBall :=
  ⟨⟨1/160, -11/32⟩, 3/320⟩
def center0559 : GaussianRat :=
  ⟨617179/125000000, -248789139/1000000000⟩
def contact0559 : RatBall := localContactBall tau0559 center0559
def work0559 : RoundedTauEval :=
  evalTau precision tau0559 contact0559 logTwoBall

theorem center_sq0559 : (center0559.re : ℝ)^2 +
    (center0559.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0559]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0559 : work0559.theta.ok = true ∧
    work0559.jac.invOK = true ∧ acceptsUnitSq work0559.out = true := by decide +kernel

def cell0559 : CellCertificate where
  tauBall := tau0559
  contactCenter := center0559
  contactBall := contact0559
  work := work0559
  center_sq := center_sq0559
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0559.1
  jac_ok := checks0559.2.1
  accepted := checks0559.2.2

def cells : List CellCertificate := [cell0552, cell0553, cell0554, cell0555, cell0556, cell0557, cell0558, cell0559]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069


