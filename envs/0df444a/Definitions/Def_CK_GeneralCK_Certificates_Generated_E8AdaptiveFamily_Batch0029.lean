-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:19:35.202307+00:00
-- url     : https://prove2.me/theorems/e3c24e9b-2f3c-4866-a21b-8f52b1387aef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0029.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact0238 : RatBall := localContactBall tau0238 center0238
def work0238 : RoundedTauEval :=
  evalTau precision tau0238 contact0238 logTwoBall

theorem center_sq0238 : (center0238.re : ℝ)^2 +
    (center0238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0238 : work0238.theta.ok = true ∧
    work0238.jac.invOK = true ∧ acceptsUnitSq work0238.out = true := by decide +kernel

def cell0238 : CellCertificate where
  tauBall := tau0238
  contactCenter := center0238
  contactBall := contact0238
  work := work0238
  center_sq := center_sq0238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0238.1
  jac_ok := checks0238.2.1
  accepted := checks0238.2.2

def tau0239 : RatBall :=
  ⟨⟨-3/16, 13/80⟩, 3/160⟩
def center0239 : GaussianRat :=
  ⟨-131822371/1000000000, 13687313/125000000⟩
def contact0239 : RatBall := localContactBall tau0239 center0239
def work0239 : RoundedTauEval :=
  evalTau precision tau0239 contact0239 logTwoBall

theorem center_sq0239 : (center0239.re : ℝ)^2 +
    (center0239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0239 : work0239.theta.ok = true ∧
    work0239.jac.invOK = true ∧ acceptsUnitSq work0239.out = true := by decide +kernel

def cell0239 : CellCertificate where
  tauBall := tau0239
  contactCenter := center0239
  contactBall := contact0239
  work := work0239
  center_sq := center_sq0239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0239.1
  jac_ok := checks0239.2.1
  accepted := checks0239.2.2

def cells : List CellCertificate := [cell0232, cell0233, cell0234, cell0235, cell0236, cell0237, cell0238, cell0239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029


