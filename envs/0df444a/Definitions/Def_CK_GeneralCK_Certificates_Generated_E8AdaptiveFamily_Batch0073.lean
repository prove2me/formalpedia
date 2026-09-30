-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:12.683835+00:00
-- url     : https://prove2.me/theorems/08fe669e-f6ef-4104-aa10-be8977f45cbc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0073.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0073_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq0589 : (center0589.re : ℝ)^2 +
    (center0589.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0589]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0589 : work0589.theta.ok = true ∧
    work0589.jac.invOK = true ∧ acceptsUnitSq work0589.out = true := by decide +kernel

def cell0589 : CellCertificate where
  tauBall := tau0589
  contactCenter := center0589
  contactBall := contact0589
  work := work0589
  center_sq := center_sq0589
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0589.1
  jac_ok := checks0589.2.1
  accepted := checks0589.2.2

def tau0590 : RatBall :=
  ⟨⟨19/160, -51/160⟩, 3/320⟩
def center0590 : GaussianRat :=
  ⟨18258621/200000000, -56322187/250000000⟩
def contact0590 : RatBall := localContactBall tau0590 center0590
def work0590 : RoundedTauEval :=
  evalTau precision tau0590 contact0590 logTwoBall

theorem center_sq0590 : (center0590.re : ℝ)^2 +
    (center0590.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0590]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0590 : work0590.theta.ok = true ∧
    work0590.jac.invOK = true ∧ acceptsUnitSq work0590.out = true := by decide +kernel

def cell0590 : CellCertificate where
  tauBall := tau0590
  contactCenter := center0590
  contactBall := contact0590
  work := work0590
  center_sq := center_sq0590
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0590.1
  jac_ok := checks0590.2.1
  accepted := checks0590.2.2

def tau0591 : RatBall :=
  ⟨⟨17/160, -49/160⟩, 3/320⟩
def center0591 : GaussianRat :=
  ⟨5068403/62500000, -846097/3906250⟩
def contact0591 : RatBall := localContactBall tau0591 center0591
def work0591 : RoundedTauEval :=
  evalTau precision tau0591 contact0591 logTwoBall

theorem center_sq0591 : (center0591.re : ℝ)^2 +
    (center0591.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0591]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0591 : work0591.theta.ok = true ∧
    work0591.jac.invOK = true ∧ acceptsUnitSq work0591.out = true := by decide +kernel

def cell0591 : CellCertificate where
  tauBall := tau0591
  contactCenter := center0591
  contactBall := contact0591
  work := work0591
  center_sq := center_sq0591
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0591.1
  jac_ok := checks0591.2.1
  accepted := checks0591.2.2

def cells : List CellCertificate := [cell0584, cell0585, cell0586, cell0587, cell0588, cell0589, cell0590, cell0591]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073


