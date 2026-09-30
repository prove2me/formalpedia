-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0036_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:15:26.986849+00:00
-- url     : https://prove2.me/theorems/45ef8c05-b39c-45b1-af1f-341984e5c394
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0036 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0288 : RatBall :=
  ⟨⟨23/80, 1/80⟩, 3/160⟩
def center0288 : GaussianRat :=
  ⟨7754861/40000000, 3988989/500000000⟩
def contact0288 : RatBall := localContactBall tau0288 center0288
def work0288 : RoundedTauEval :=
  evalTau precision tau0288 contact0288 logTwoBall

theorem center_sq0288 : (center0288.re : ℝ)^2 +
    (center0288.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0288]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0288 : work0288.theta.ok = true ∧
    work0288.jac.invOK = true ∧ acceptsUnitSq work0288.out = true := by decide +kernel

def cell0288 : CellCertificate where
  tauBall := tau0288
  contactCenter := center0288
  contactBall := contact0288
  work := work0288
  center_sq := center_sq0288
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0288.1
  jac_ok := checks0288.2.1
  accepted := checks0288.2.2

def tau0289 : RatBall :=
  ⟨⟨21/80, 3/80⟩, 3/160⟩
def center0289 : GaussianRat :=
  ⟨89006593/500000000, 4852281/200000000⟩
def contact0289 : RatBall := localContactBall tau0289 center0289
def work0289 : RoundedTauEval :=
  evalTau precision tau0289 contact0289 logTwoBall

theorem center_sq0289 : (center0289.re : ℝ)^2 +
    (center0289.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0289]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0289 : work0289.theta.ok = true ∧
    work0289.jac.invOK = true ∧ acceptsUnitSq work0289.out = true := by decide +kernel

def cell0289 : CellCertificate where
  tauBall := tau0289
  contactCenter := center0289
  contactBall := contact0289
  work := work0289
  center_sq := center_sq0289
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0289.1
  jac_ok := checks0289.2.1
  accepted := checks0289.2.2

def tau0290 : RatBall :=
  ⟨⟨23/80, 3/80⟩, 3/160⟩
def center0290 : GaussianRat :=
  ⟨4852301/25000000, 23940531/1000000000⟩
def contact0290 : RatBall := localContactBall tau0290 center0290
def work0290 : RoundedTauEval :=
  evalTau precision tau0290 contact0290 logTwoBall

theorem center_sq0290 : (center0290.re : ℝ)^2 +
    (center0290.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0290]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0290 : work0290.theta.ok = true ∧
    work0290.jac.invOK = true ∧ acceptsUnitSq work0290.out = true := by decide +kernel

def cell0290 : CellCertificate where
  tauBall := tau0290
  contactCenter := center0290
  contactBall := contact0290
  work := work0290
  center_sq := center_sq0290
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0290.1
  jac_ok := checks0290.2.1
  accepted := checks0290.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036


