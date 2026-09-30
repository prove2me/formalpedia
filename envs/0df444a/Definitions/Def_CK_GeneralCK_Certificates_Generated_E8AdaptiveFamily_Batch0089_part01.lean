-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:46:12.846212+00:00
-- url     : https://prove2.me/theorems/7091c049-3046-49ec-b3f2-01972e235f1b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0089 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0089_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0715 : RatBall :=
  ⟨⟨53/160, -31/160⟩, 3/320⟩
def center0715 : GaussianRat :=
  ⟨114433899/500000000, -30340451/250000000⟩
def contact0715 : RatBall := localContactBall tau0715 center0715
def work0715 : RoundedTauEval :=
  evalTau precision tau0715 contact0715 logTwoBall

theorem center_sq0715 : (center0715.re : ℝ)^2 +
    (center0715.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0715]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0715 : work0715.theta.ok = true ∧
    work0715.jac.invOK = true ∧ acceptsUnitSq work0715.out = true := by decide +kernel

def cell0715 : CellCertificate where
  tauBall := tau0715
  contactCenter := center0715
  contactBall := contact0715
  work := work0715
  center_sq := center_sq0715
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0715.1
  jac_ok := checks0715.2.1
  accepted := checks0715.2.2

def tau0716 : RatBall :=
  ⟨⟨11/32, -31/160⟩, 3/320⟩
def center0716 : GaussianRat :=
  ⟨47354053/200000000, -30090849/250000000⟩
def contact0716 : RatBall := localContactBall tau0716 center0716
def work0716 : RoundedTauEval :=
  evalTau precision tau0716 contact0716 logTwoBall

theorem center_sq0716 : (center0716.re : ℝ)^2 +
    (center0716.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0716]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0716 : work0716.theta.ok = true ∧
    work0716.jac.invOK = true ∧ acceptsUnitSq work0716.out = true := by decide +kernel

def cell0716 : CellCertificate where
  tauBall := tau0716
  contactCenter := center0716
  contactBall := contact0716
  work := work0716
  center_sq := center_sq0716
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0716.1
  jac_ok := checks0716.2.1
  accepted := checks0716.2.2

def tau0717 : RatBall :=
  ⟨⟨53/160, -29/160⟩, 3/320⟩
def center0717 : GaussianRat :=
  ⟨227914773/1000000000, -56716957/500000000⟩
def contact0717 : RatBall := localContactBall tau0717 center0717
def work0717 : RoundedTauEval :=
  evalTau precision tau0717 contact0717 logTwoBall

theorem center_sq0717 : (center0717.re : ℝ)^2 +
    (center0717.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0717]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0717 : work0717.theta.ok = true ∧
    work0717.jac.invOK = true ∧ acceptsUnitSq work0717.out = true := by decide +kernel

def cell0717 : CellCertificate where
  tauBall := tau0717
  contactCenter := center0717
  contactBall := contact0717
  work := work0717
  center_sq := center_sq0717
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0717.1
  jac_ok := checks0717.2.1
  accepted := checks0717.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089


