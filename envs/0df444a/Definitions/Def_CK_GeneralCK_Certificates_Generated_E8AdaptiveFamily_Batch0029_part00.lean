-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0029_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:14:48.214315+00:00
-- url     : https://prove2.me/theorems/0c818027-9366-41cc-992d-577ff0f4199d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0029 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0232 : RatBall :=
  ⟨⟨-19/80, 13/80⟩, 3/160⟩
def center0232 : GaussianRat :=
  ⟨-41411389/250000000, 107116873/1000000000⟩
def contact0232 : RatBall := localContactBall tau0232 center0232
def work0232 : RoundedTauEval :=
  evalTau precision tau0232 contact0232 logTwoBall

theorem center_sq0232 : (center0232.re : ℝ)^2 +
    (center0232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0232 : work0232.theta.ok = true ∧
    work0232.jac.invOK = true ∧ acceptsUnitSq work0232.out = true := by decide +kernel

def cell0232 : CellCertificate where
  tauBall := tau0232
  contactCenter := center0232
  contactBall := contact0232
  work := work0232
  center_sq := center_sq0232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0232.1
  jac_ok := checks0232.2.1
  accepted := checks0232.2.2

def tau0233 : RatBall :=
  ⟨⟨-17/80, 13/80⟩, 3/160⟩
def center0233 : GaussianRat :=
  ⟨-148834391/1000000000, 27091123/250000000⟩
def contact0233 : RatBall := localContactBall tau0233 center0233
def work0233 : RoundedTauEval :=
  evalTau precision tau0233 contact0233 logTwoBall

theorem center_sq0233 : (center0233.re : ℝ)^2 +
    (center0233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0233 : work0233.theta.ok = true ∧
    work0233.jac.invOK = true ∧ acceptsUnitSq work0233.out = true := by decide +kernel

def cell0233 : CellCertificate where
  tauBall := tau0233
  contactCenter := center0233
  contactBall := contact0233
  work := work0233
  center_sq := center_sq0233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0233.1
  jac_ok := checks0233.2.1
  accepted := checks0233.2.2

def tau0234 : RatBall :=
  ⟨⟨-17/80, 3/16⟩, 3/160⟩
def center0234 : GaussianRat :=
  ⟨-150128589/1000000000, 25067823/200000000⟩
def contact0234 : RatBall := localContactBall tau0234 center0234
def work0234 : RoundedTauEval :=
  evalTau precision tau0234 contact0234 logTwoBall

theorem center_sq0234 : (center0234.re : ℝ)^2 +
    (center0234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0234 : work0234.theta.ok = true ∧
    work0234.jac.invOK = true ∧ acceptsUnitSq work0234.out = true := by decide +kernel

def cell0234 : CellCertificate where
  tauBall := tau0234
  contactCenter := center0234
  contactBall := contact0234
  work := work0234
  center_sq := center_sq0234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0234.1
  jac_ok := checks0234.2.1
  accepted := checks0234.2.2

def tau0235 : RatBall :=
  ⟨⟨-3/16, 9/80⟩, 3/160⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029


