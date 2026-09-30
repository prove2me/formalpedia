-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0033_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:12:48.852348+00:00
-- url     : https://prove2.me/theorems/ad769d07-0d62-42bd-8eb4-0f0f4e8eae9a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0033 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0264 : RatBall :=
  ⟨⟨-1/80, 19/80⟩, 3/160⟩
def center0264 : GaussianRat :=
  ⟨-1150363/125000000, 41981661/250000000⟩
def contact0264 : RatBall := localContactBall tau0264 center0264
def work0264 : RoundedTauEval :=
  evalTau precision tau0264 contact0264 logTwoBall

theorem center_sq0264 : (center0264.re : ℝ)^2 +
    (center0264.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0264]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0264 : work0264.theta.ok = true ∧
    work0264.jac.invOK = true ∧ acceptsUnitSq work0264.out = true := by decide +kernel

def cell0264 : CellCertificate where
  tauBall := tau0264
  contactCenter := center0264
  contactBall := contact0264
  work := work0264
  center_sq := center_sq0264
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0264.1
  jac_ok := checks0264.2.1
  accepted := checks0264.2.2

def tau0265 : RatBall :=
  ⟨⟨-7/80, 21/80⟩, 3/160⟩
def center0265 : GaussianRat :=
  ⟨-6508393/100000000, 184829567/1000000000⟩
def contact0265 : RatBall := localContactBall tau0265 center0265
def work0265 : RoundedTauEval :=
  evalTau precision tau0265 contact0265 logTwoBall

theorem center_sq0265 : (center0265.re : ℝ)^2 +
    (center0265.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0265]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0265 : work0265.theta.ok = true ∧
    work0265.jac.invOK = true ∧ acceptsUnitSq work0265.out = true := by decide +kernel

def cell0265 : CellCertificate where
  tauBall := tau0265
  contactCenter := center0265
  contactBall := contact0265
  work := work0265
  center_sq := center_sq0265
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0265.1
  jac_ok := checks0265.2.1
  accepted := checks0265.2.2

def tau0266 : RatBall :=
  ⟨⟨-1/16, 21/80⟩, 3/160⟩
def center0266 : GaussianRat :=
  ⟨-46572457/1000000000, 46409673/250000000⟩
def contact0266 : RatBall := localContactBall tau0266 center0266
def work0266 : RoundedTauEval :=
  evalTau precision tau0266 contact0266 logTwoBall

theorem center_sq0266 : (center0266.re : ℝ)^2 +
    (center0266.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0266]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0266 : work0266.theta.ok = true ∧
    work0266.jac.invOK = true ∧ acceptsUnitSq work0266.out = true := by decide +kernel

def cell0266 : CellCertificate where
  tauBall := tau0266
  contactCenter := center0266
  contactBall := contact0266
  work := work0266
  center_sq := center_sq0266
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0266.1
  jac_ok := checks0266.2.1
  accepted := checks0266.2.2

def tau0267 : RatBall :=
  ⟨⟨-3/80, 21/80⟩, 3/160⟩
def center0267 : GaussianRat :=
  ⟨-27977261/1000000000, 186182371/1000000000⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033


