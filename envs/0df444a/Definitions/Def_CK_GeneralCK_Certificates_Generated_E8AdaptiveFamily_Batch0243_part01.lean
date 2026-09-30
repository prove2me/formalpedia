-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:17:09.551291+00:00
-- url     : https://prove2.me/theorems/9322d8db-0b13-4073-b57b-d500ba89b74e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0243 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0243_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def work1946 : RoundedTauEval :=
  evalTau precision tau1946 contact1946 logTwoBall

theorem center_sq1946 : (center1946.re : ℝ)^2 +
    (center1946.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1946]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1946 : work1946.theta.ok = true ∧
    work1946.jac.invOK = true ∧ acceptsUnitSq work1946.out = true := by decide +kernel

def cell1946 : CellCertificate where
  tauBall := tau1946
  contactCenter := center1946
  contactBall := contact1946
  work := work1946
  center_sq := center_sq1946
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1946.1
  jac_ok := checks1946.2.1
  accepted := checks1946.2.2

def tau1947 : RatBall :=
  ⟨⟨-83/320, 89/320⟩, 3/640⟩
def center1947 : GaussianRat :=
  ⟨-189282071/1000000000, 183581561/1000000000⟩
def contact1947 : RatBall := localContactBall tau1947 center1947
def work1947 : RoundedTauEval :=
  evalTau precision tau1947 contact1947 logTwoBall

theorem center_sq1947 : (center1947.re : ℝ)^2 +
    (center1947.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1947]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1947 : work1947.theta.ok = true ∧
    work1947.jac.invOK = true ∧ acceptsUnitSq work1947.out = true := by decide +kernel

def cell1947 : CellCertificate where
  tauBall := tau1947
  contactCenter := center1947
  contactBall := contact1947
  work := work1947
  center_sq := center_sq1947
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1947.1
  jac_ok := checks1947.2.1
  accepted := checks1947.2.2

def tau1948 : RatBall :=
  ⟨⟨-81/320, 89/320⟩, 3/640⟩
def center1948 : GaussianRat :=
  ⟨-92495743/500000000, 184225151/1000000000⟩
def contact1948 : RatBall := localContactBall tau1948 center1948
def work1948 : RoundedTauEval :=
  evalTau precision tau1948 contact1948 logTwoBall

theorem center_sq1948 : (center1948.re : ℝ)^2 +
    (center1948.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1948]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1948 : work1948.theta.ok = true ∧
    work1948.jac.invOK = true ∧ acceptsUnitSq work1948.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243


