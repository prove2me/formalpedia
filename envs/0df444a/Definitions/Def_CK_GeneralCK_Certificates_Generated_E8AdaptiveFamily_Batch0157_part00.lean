-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:13:47.279374+00:00
-- url     : https://prove2.me/theorems/7d1fd1f6-cf50-472d-b1e4-0f4c2e460fcd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0157 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1256 : RatBall :=
  ⟨⟨-99/320, -77/320⟩, 3/640⟩
def center1256 : GaussianRat :=
  ⟨-218923989/1000000000, -38365123/250000000⟩
def contact1256 : RatBall := localContactBall tau1256 center1256
def work1256 : RoundedTauEval :=
  evalTau precision tau1256 contact1256 logTwoBall

theorem center_sq1256 : (center1256.re : ℝ)^2 +
    (center1256.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1256]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1256 : work1256.theta.ok = true ∧
    work1256.jac.invOK = true ∧ acceptsUnitSq work1256.out = true := by decide +kernel

def cell1256 : CellCertificate where
  tauBall := tau1256
  contactCenter := center1256
  contactBall := contact1256
  work := work1256
  center_sq := center_sq1256
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1256.1
  jac_ok := checks1256.2.1
  accepted := checks1256.2.2

def tau1257 : RatBall :=
  ⟨⟨-97/320, -77/320⟩, 3/640⟩
def center1257 : GaussianRat :=
  ⟨-10741779/50000000, -300909/1953125⟩
def contact1257 : RatBall := localContactBall tau1257 center1257
def work1257 : RoundedTauEval :=
  evalTau precision tau1257 contact1257 logTwoBall

theorem center_sq1257 : (center1257.re : ℝ)^2 +
    (center1257.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1257]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1257 : work1257.theta.ok = true ∧
    work1257.jac.invOK = true ∧ acceptsUnitSq work1257.out = true := by decide +kernel

def cell1257 : CellCertificate where
  tauBall := tau1257
  contactCenter := center1257
  contactBall := contact1257
  work := work1257
  center_sq := center_sq1257
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1257.1
  jac_ok := checks1257.2.1
  accepted := checks1257.2.2

def tau1258 : RatBall :=
  ⟨⟨-103/320, -15/64⟩, 3/640⟩
def center1258 : GaussianRat :=
  ⟨-14151969/62500000, -148191091/1000000000⟩
def contact1258 : RatBall := localContactBall tau1258 center1258
def work1258 : RoundedTauEval :=
  evalTau precision tau1258 contact1258 logTwoBall

theorem center_sq1258 : (center1258.re : ℝ)^2 +
    (center1258.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1258]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1258 : work1258.theta.ok = true ∧
    work1258.jac.invOK = true ∧ acceptsUnitSq work1258.out = true := by decide +kernel

def cell1258 : CellCertificate where
  tauBall := tau1258
  contactCenter := center1258
  contactBall := contact1258
  work := work1258
  center_sq := center_sq1258
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1258.1
  jac_ok := checks1258.2.1
  accepted := checks1258.2.2

def tau1259 : RatBall :=
  ⟨⟨-101/320, -15/64⟩, 3/640⟩
def center1259 : GaussianRat :=
  ⟨-13899213/62500000, -2975829/20000000⟩
def contact1259 : RatBall := localContactBall tau1259 center1259
def work1259 : RoundedTauEval :=
  evalTau precision tau1259 contact1259 logTwoBall

theorem center_sq1259 : (center1259.re : ℝ)^2 +
    (center1259.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1259]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1259 : work1259.theta.ok = true ∧
    work1259.jac.invOK = true ∧ acceptsUnitSq work1259.out = true := by decide +kernel

def cell1259 : CellCertificate where
  tauBall := tau1259
  contactCenter := center1259
  contactBall := contact1259
  work := work1259
  center_sq := center_sq1259
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1259.1
  jac_ok := checks1259.2.1
  accepted := checks1259.2.2

def tau1260 : RatBall :=
  ⟨⟨-103/320, -73/320⟩, 3/640⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157


