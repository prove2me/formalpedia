-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0159_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:18:11.695966+00:00
-- url     : https://prove2.me/theorems/a1cb0ae3-3aa4-49bc-a3d1-c5e598b8db5e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0159 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1272 : RatBall :=
  ⟨⟨-91/320, -91/320⟩, 3/640⟩
def center1272 : GaussianRat :=
  ⟨-51739029/250000000, -46278317/250000000⟩
def contact1272 : RatBall := localContactBall tau1272 center1272
def work1272 : RoundedTauEval :=
  evalTau precision tau1272 contact1272 logTwoBall

theorem center_sq1272 : (center1272.re : ℝ)^2 +
    (center1272.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1272]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1272 : work1272.theta.ok = true ∧
    work1272.jac.invOK = true ∧ acceptsUnitSq work1272.out = true := by decide +kernel

def cell1272 : CellCertificate where
  tauBall := tau1272
  contactCenter := center1272
  contactBall := contact1272
  work := work1272
  center_sq := center_sq1272
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1272.1
  jac_ok := checks1272.2.1
  accepted := checks1272.2.2

def tau1273 : RatBall :=
  ⟨⟨-89/320, -91/320⟩, 3/640⟩
def center1273 : GaussianRat :=
  ⟨-202731249/1000000000, -37163483/200000000⟩
def contact1273 : RatBall := localContactBall tau1273 center1273
def work1273 : RoundedTauEval :=
  evalTau precision tau1273 contact1273 logTwoBall

theorem center_sq1273 : (center1273.re : ℝ)^2 +
    (center1273.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1273]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1273 : work1273.theta.ok = true ∧
    work1273.jac.invOK = true ∧ acceptsUnitSq work1273.out = true := by decide +kernel

def cell1273 : CellCertificate where
  tauBall := tau1273
  contactCenter := center1273
  contactBall := contact1273
  work := work1273
  center_sq := center_sq1273
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1273.1
  jac_ok := checks1273.2.1
  accepted := checks1273.2.2

def tau1274 : RatBall :=
  ⟨⟨-91/320, -89/320⟩, 3/640⟩
def center1274 : GaussianRat :=
  ⟨-103128439/500000000, -180903081/1000000000⟩
def contact1274 : RatBall := localContactBall tau1274 center1274
def work1274 : RoundedTauEval :=
  evalTau precision tau1274 contact1274 logTwoBall

theorem center_sq1274 : (center1274.re : ℝ)^2 +
    (center1274.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1274]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1274 : work1274.theta.ok = true ∧
    work1274.jac.invOK = true ∧ acceptsUnitSq work1274.out = true := by decide +kernel

def cell1274 : CellCertificate where
  tauBall := tau1274
  contactCenter := center1274
  contactBall := contact1274
  work := work1274
  center_sq := center_sq1274
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1274.1
  jac_ok := checks1274.2.1
  accepted := checks1274.2.2

def tau1275 : RatBall :=
  ⟨⟨-89/320, -89/320⟩, 3/640⟩
def center1275 : GaussianRat :=
  ⟨-40408359/200000000, -181587727/1000000000⟩
def contact1275 : RatBall := localContactBall tau1275 center1275
def work1275 : RoundedTauEval :=
  evalTau precision tau1275 contact1275 logTwoBall

theorem center_sq1275 : (center1275.re : ℝ)^2 +
    (center1275.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1275]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1275 : work1275.theta.ok = true ∧
    work1275.jac.invOK = true ∧ acceptsUnitSq work1275.out = true := by decide +kernel

def cell1275 : CellCertificate where
  tauBall := tau1275
  contactCenter := center1275
  contactBall := contact1275
  work := work1275
  center_sq := center_sq1275
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1275.1
  jac_ok := checks1275.2.1
  accepted := checks1275.2.2

def tau1276 : RatBall :=
  ⟨⟨-87/320, -19/64⟩, 3/640⟩
def center1276 : GaussianRat :=
  ⟨-199903813/1000000000, -195040739/1000000000⟩
def contact1276 : RatBall := localContactBall tau1276 center1276
def work1276 : RoundedTauEval :=
  evalTau precision tau1276 contact1276 logTwoBall

theorem center_sq1276 : (center1276.re : ℝ)^2 +
    (center1276.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1276]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1276 : work1276.theta.ok = true ∧
    work1276.jac.invOK = true ∧ acceptsUnitSq work1276.out = true := by decide +kernel

def cell1276 : CellCertificate where
  tauBall := tau1276
  contactCenter := center1276
  contactBall := contact1276
  work := work1276
  center_sq := center_sq1276
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1276.1
  jac_ok := checks1276.2.1
  accepted := checks1276.2.2

def tau1277 : RatBall :=
  ⟨⟨-17/64, -19/64⟩, 3/640⟩
def center1277 : GaussianRat :=
  ⟨-39123719/200000000, -48940869/250000000⟩
def contact1277 : RatBall := localContactBall tau1277 center1277
def work1277 : RoundedTauEval :=
  evalTau precision tau1277 contact1277 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159


