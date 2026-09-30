-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:39:12.952399+00:00
-- url     : https://prove2.me/theorems/569f6cf6-1fea-4edd-96a2-cd0c0df5f22b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0120 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0120_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0964 : RatBall :=
  ⟨⟨-3/32, 53/160⟩, 3/320⟩
def center0964 : GaussianRat :=
  ⟨-72958787/1000000000, 47269393/200000000⟩
def contact0964 : RatBall := localContactBall tau0964 center0964
def work0964 : RoundedTauEval :=
  evalTau precision tau0964 contact0964 logTwoBall

theorem center_sq0964 : (center0964.re : ℝ)^2 +
    (center0964.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0964]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0964 : work0964.theta.ok = true ∧
    work0964.jac.invOK = true ∧ acceptsUnitSq work0964.out = true := by decide +kernel

def cell0964 : CellCertificate where
  tauBall := tau0964
  contactCenter := center0964
  contactBall := contact0964
  work := work0964
  center_sq := center_sq0964
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0964.1
  jac_ok := checks0964.2.1
  accepted := checks0964.2.2

def tau0965 : RatBall :=
  ⟨⟨-13/160, 53/160⟩, 3/320⟩
def center0965 : GaussianRat :=
  ⟨-63310961/1000000000, 236995059/1000000000⟩
def contact0965 : RatBall := localContactBall tau0965 center0965
def work0965 : RoundedTauEval :=
  evalTau precision tau0965 contact0965 logTwoBall

theorem center_sq0965 : (center0965.re : ℝ)^2 +
    (center0965.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0965]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0965 : work0965.theta.ok = true ∧
    work0965.jac.invOK = true ∧ acceptsUnitSq work0965.out = true := by decide +kernel

def cell0965 : CellCertificate where
  tauBall := tau0965
  contactCenter := center0965
  contactBall := contact0965
  work := work0965
  center_sq := center_sq0965
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0965.1
  jac_ok := checks0965.2.1
  accepted := checks0965.2.2

def tau0966 : RatBall :=
  ⟨⟨-11/160, 53/160⟩, 3/320⟩
def center0966 : GaussianRat :=
  ⟨-53629143/1000000000, 118776899/500000000⟩
def contact0966 : RatBall := localContactBall tau0966 center0966
def work0966 : RoundedTauEval :=
  evalTau precision tau0966 contact0966 logTwoBall

theorem center_sq0966 : (center0966.re : ℝ)^2 +
    (center0966.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0966]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0966 : work0966.theta.ok = true ∧
    work0966.jac.invOK = true ∧ acceptsUnitSq work0966.out = true := by decide +kernel

def cell0966 : CellCertificate where
  tauBall := tau0966
  contactCenter := center0966
  contactBall := contact0966
  work := work0966
  center_sq := center_sq0966
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0966.1
  jac_ok := checks0966.2.1
  accepted := checks0966.2.2

def tau0967 : RatBall :=
  ⟨⟨-9/160, 53/160⟩, 3/320⟩
def center0967 : GaussianRat :=
  ⟨-43918333/1000000000, 238021713/1000000000⟩
def contact0967 : RatBall := localContactBall tau0967 center0967
def work0967 : RoundedTauEval :=
  evalTau precision tau0967 contact0967 logTwoBall

theorem center_sq0967 : (center0967.re : ℝ)^2 +
    (center0967.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0967]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0967 : work0967.theta.ok = true ∧
    work0967.jac.invOK = true ∧ acceptsUnitSq work0967.out = true := by decide +kernel

def cell0967 : CellCertificate where
  tauBall := tau0967
  contactCenter := center0967
  contactBall := contact0967
  work := work0967
  center_sq := center_sq0967
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0967.1
  jac_ok := checks0967.2.1
  accepted := checks0967.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120


