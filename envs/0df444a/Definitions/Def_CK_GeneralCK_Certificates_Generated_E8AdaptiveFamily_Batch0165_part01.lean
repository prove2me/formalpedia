-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:16:42.99226+00:00
-- url     : https://prove2.me/theorems/9590c47f-8d90-4149-b853-34d9e4edaf17
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0165 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0165_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell1323 : CellCertificate where
  tauBall := tau1323
  contactCenter := center1323
  contactBall := contact1323
  work := work1323
  center_sq := center_sq1323
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1323.1
  jac_ok := checks1323.2.1
  accepted := checks1323.2.2

def tau1324 : RatBall :=
  ⟨⟨-79/320, -91/320⟩, 3/640⟩
def center1324 : GaussianRat :=
  ⟨-181318681/1000000000, -189181283/1000000000⟩
def contact1324 : RatBall := localContactBall tau1324 center1324
def work1324 : RoundedTauEval :=
  evalTau precision tau1324 contact1324 logTwoBall

theorem center_sq1324 : (center1324.re : ℝ)^2 +
    (center1324.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1324]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1324 : work1324.theta.ok = true ∧
    work1324.jac.invOK = true ∧ acceptsUnitSq work1324.out = true := by decide +kernel

def cell1324 : CellCertificate where
  tauBall := tau1324
  contactCenter := center1324
  contactBall := contact1324
  work := work1324
  center_sq := center_sq1324
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1324.1
  jac_ok := checks1324.2.1
  accepted := checks1324.2.2

def tau1325 : RatBall :=
  ⟨⟨-77/320, -91/320⟩, 3/640⟩
def center1325 : GaussianRat :=
  ⟨-17698031/100000000, -94910271/500000000⟩
def contact1325 : RatBall := localContactBall tau1325 center1325
def work1325 : RoundedTauEval :=
  evalTau precision tau1325 contact1325 logTwoBall

theorem center_sq1325 : (center1325.re : ℝ)^2 +
    (center1325.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1325]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1325 : work1325.theta.ok = true ∧
    work1325.jac.invOK = true ∧ acceptsUnitSq work1325.out = true := by decide +kernel

def cell1325 : CellCertificate where
  tauBall := tau1325
  contactCenter := center1325
  contactBall := contact1325
  work := work1325
  center_sq := center_sq1325
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1325.1
  jac_ok := checks1325.2.1
  accepted := checks1325.2.2

def tau1326 : RatBall :=
  ⟨⟨-79/320, -89/320⟩, 3/640⟩
def center1326 : GaussianRat :=
  ⟨-22585333/125000000, -184857737/1000000000⟩
def contact1326 : RatBall := localContactBall tau1326 center1326
def work1326 : RoundedTauEval :=
  evalTau precision tau1326 contact1326 logTwoBall

theorem center_sq1326 : (center1326.re : ℝ)^2 +
    (center1326.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1326]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1326 : work1326.theta.ok = true ∧
    work1326.jac.invOK = true ∧ acceptsUnitSq work1326.out = true := by decide +kernel

def cell1326 : CellCertificate where
  tauBall := tau1326
  contactCenter := center1326
  contactBall := contact1326
  work := work1326
  center_sq := center_sq1326
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1326.1
  jac_ok := checks1326.2.1
  accepted := checks1326.2.2

def tau1327 : RatBall :=
  ⟨⟨-77/320, -89/320⟩, 3/640⟩
def center1327 : GaussianRat :=
  ⟨-88177939/500000000, -185479027/1000000000⟩
def contact1327 : RatBall := localContactBall tau1327 center1327
def work1327 : RoundedTauEval :=
  evalTau precision tau1327 contact1327 logTwoBall

theorem center_sq1327 : (center1327.re : ℝ)^2 +
    (center1327.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1327]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165


