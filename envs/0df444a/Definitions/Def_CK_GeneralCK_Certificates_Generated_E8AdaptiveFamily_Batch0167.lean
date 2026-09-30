-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:05:44.272162+00:00
-- url     : https://prove2.me/theorems/b46b9914-f5b3-483e-8821-c58da9a5df3d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0167.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0167_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1340 : work1340.theta.ok = true ∧
    work1340.jac.invOK = true ∧ acceptsUnitSq work1340.out = true := by decide +kernel

def cell1340 : CellCertificate where
  tauBall := tau1340
  contactCenter := center1340
  contactBall := contact1340
  work := work1340
  center_sq := center_sq1340
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1340.1
  jac_ok := checks1340.2.1
  accepted := checks1340.2.2

def tau1341 : RatBall :=
  ⟨⟨-93/320, -79/320⟩, 3/640⟩
def center1341 : GaussianRat :=
  ⟨-207198371/1000000000, -15939079/100000000⟩
def contact1341 : RatBall := localContactBall tau1341 center1341
def work1341 : RoundedTauEval :=
  evalTau precision tau1341 contact1341 logTwoBall

theorem center_sq1341 : (center1341.re : ℝ)^2 +
    (center1341.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1341]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1341 : work1341.theta.ok = true ∧
    work1341.jac.invOK = true ∧ acceptsUnitSq work1341.out = true := by decide +kernel

def cell1341 : CellCertificate where
  tauBall := tau1341
  contactCenter := center1341
  contactBall := contact1341
  work := work1341
  center_sq := center_sq1341
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1341.1
  jac_ok := checks1341.2.1
  accepted := checks1341.2.2

def tau1342 : RatBall :=
  ⟨⟨-19/64, -77/320⟩, 3/640⟩
def center1342 : GaussianRat :=
  ⟨-26341087/125000000, -77331419/500000000⟩
def contact1342 : RatBall := localContactBall tau1342 center1342
def work1342 : RoundedTauEval :=
  evalTau precision tau1342 contact1342 logTwoBall

theorem center_sq1342 : (center1342.re : ℝ)^2 +
    (center1342.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1342]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1342 : work1342.theta.ok = true ∧
    work1342.jac.invOK = true ∧ acceptsUnitSq work1342.out = true := by decide +kernel

def cell1342 : CellCertificate where
  tauBall := tau1342
  contactCenter := center1342
  contactBall := contact1342
  work := work1342
  center_sq := center_sq1342
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1342.1
  jac_ok := checks1342.2.1
  accepted := checks1342.2.2

def tau1343 : RatBall :=
  ⟨⟨-93/320, -77/320⟩, 3/640⟩
def center1343 : GaussianRat :=
  ⟨-12912721/62500000, -7762627/50000000⟩
def contact1343 : RatBall := localContactBall tau1343 center1343
def work1343 : RoundedTauEval :=
  evalTau precision tau1343 contact1343 logTwoBall

theorem center_sq1343 : (center1343.re : ℝ)^2 +
    (center1343.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1343]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1343 : work1343.theta.ok = true ∧
    work1343.jac.invOK = true ∧ acceptsUnitSq work1343.out = true := by decide +kernel

def cell1343 : CellCertificate where
  tauBall := tau1343
  contactCenter := center1343
  contactBall := contact1343
  work := work1343
  center_sq := center_sq1343
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1343.1
  jac_ok := checks1343.2.1
  accepted := checks1343.2.2

def cells : List CellCertificate := [cell1336, cell1337, cell1338, cell1339, cell1340, cell1341, cell1342, cell1343]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167


