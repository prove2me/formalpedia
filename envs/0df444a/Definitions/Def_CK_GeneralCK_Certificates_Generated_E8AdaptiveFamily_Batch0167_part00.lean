-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:25:57.358448+00:00
-- url     : https://prove2.me/theorems/8865207d-e722-4d6d-8c73-773ac742e9e9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0167 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1336 : RatBall :=
  ⟨⟨-67/320, -19/64⟩, 3/640⟩
def center1336 : GaussianRat :=
  ⟨-78099293/500000000, -100863299/500000000⟩
def contact1336 : RatBall := localContactBall tau1336 center1336
def work1336 : RoundedTauEval :=
  evalTau precision tau1336 contact1336 logTwoBall

theorem center_sq1336 : (center1336.re : ℝ)^2 +
    (center1336.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1336]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1336 : work1336.theta.ok = true ∧
    work1336.jac.invOK = true ∧ acceptsUnitSq work1336.out = true := by decide +kernel

def cell1336 : CellCertificate where
  tauBall := tau1336
  contactCenter := center1336
  contactBall := contact1336
  work := work1336
  center_sq := center_sq1336
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1336.1
  jac_ok := checks1336.2.1
  accepted := checks1336.2.2

def tau1337 : RatBall :=
  ⟨⟨-13/64, -19/64⟩, 3/640⟩
def center1337 : GaussianRat :=
  ⟨-30345869/200000000, -40464617/200000000⟩
def contact1337 : RatBall := localContactBall tau1337 center1337
def work1337 : RoundedTauEval :=
  evalTau precision tau1337 contact1337 logTwoBall

theorem center_sq1337 : (center1337.re : ℝ)^2 +
    (center1337.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1337]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1337 : work1337.theta.ok = true ∧
    work1337.jac.invOK = true ∧ acceptsUnitSq work1337.out = true := by decide +kernel

def cell1337 : CellCertificate where
  tauBall := tau1337
  contactCenter := center1337
  contactBall := contact1337
  work := work1337
  center_sq := center_sq1337
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1337.1
  jac_ok := checks1337.2.1
  accepted := checks1337.2.2

def tau1338 : RatBall :=
  ⟨⟨-67/320, -93/320⟩, 3/640⟩
def center1338 : GaussianRat :=
  ⟨-3112069/20000000, -197272757/1000000000⟩
def contact1338 : RatBall := localContactBall tau1338 center1338
def work1338 : RoundedTauEval :=
  evalTau precision tau1338 contact1338 logTwoBall

theorem center_sq1338 : (center1338.re : ℝ)^2 +
    (center1338.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1338]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1338 : work1338.theta.ok = true ∧
    work1338.jac.invOK = true ∧ acceptsUnitSq work1338.out = true := by decide +kernel

def cell1338 : CellCertificate where
  tauBall := tau1338
  contactCenter := center1338
  contactBall := contact1338
  work := work1338
  center_sq := center_sq1338
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1338.1
  jac_ok := checks1338.2.1
  accepted := checks1338.2.2

def tau1339 : RatBall :=
  ⟨⟨-13/64, -93/320⟩, 3/640⟩
def center1339 : GaussianRat :=
  ⟨-151148249/1000000000, -98926301/500000000⟩
def contact1339 : RatBall := localContactBall tau1339 center1339
def work1339 : RoundedTauEval :=
  evalTau precision tau1339 contact1339 logTwoBall

theorem center_sq1339 : (center1339.re : ℝ)^2 +
    (center1339.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1339]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1339 : work1339.theta.ok = true ∧
    work1339.jac.invOK = true ∧ acceptsUnitSq work1339.out = true := by decide +kernel

def cell1339 : CellCertificate where
  tauBall := tau1339
  contactCenter := center1339
  contactBall := contact1339
  work := work1339
  center_sq := center_sq1339
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1339.1
  jac_ok := checks1339.2.1
  accepted := checks1339.2.2

def tau1340 : RatBall :=
  ⟨⟨-19/64, -79/320⟩, 3/640⟩
def center1340 : GaussianRat :=
  ⟨-211331481/1000000000, -158782791/1000000000⟩
def contact1340 : RatBall := localContactBall tau1340 center1340
def work1340 : RoundedTauEval :=
  evalTau precision tau1340 contact1340 logTwoBall

theorem center_sq1340 : (center1340.re : ℝ)^2 +
    (center1340.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1340]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167


