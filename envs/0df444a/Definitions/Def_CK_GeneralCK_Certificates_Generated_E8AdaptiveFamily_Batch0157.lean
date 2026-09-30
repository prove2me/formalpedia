-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:39:56.347175+00:00
-- url     : https://prove2.me/theorems/c82f4f09-c175-446d-82ae-6e146aae0947
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0157.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0157_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center1260 : GaussianRat :=
  ⟨-5645929/25000000, -9009977/62500000⟩
def contact1260 : RatBall := localContactBall tau1260 center1260
def work1260 : RoundedTauEval :=
  evalTau precision tau1260 contact1260 logTwoBall

theorem center_sq1260 : (center1260.re : ℝ)^2 +
    (center1260.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1260]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1260 : work1260.theta.ok = true ∧
    work1260.jac.invOK = true ∧ acceptsUnitSq work1260.out = true := by decide +kernel

def cell1260 : CellCertificate where
  tauBall := tau1260
  contactCenter := center1260
  contactBall := contact1260
  work := work1260
  center_sq := center_sq1260
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1260.1
  jac_ok := checks1260.2.1
  accepted := checks1260.2.2

def tau1261 : RatBall :=
  ⟨⟨-101/320, -73/320⟩, 3/640⟩
def center1261 : GaussianRat :=
  ⟨-44359939/200000000, -72370703/500000000⟩
def contact1261 : RatBall := localContactBall tau1261 center1261
def work1261 : RoundedTauEval :=
  evalTau precision tau1261 contact1261 logTwoBall

theorem center_sq1261 : (center1261.re : ℝ)^2 +
    (center1261.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1261]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1261 : work1261.theta.ok = true ∧
    work1261.jac.invOK = true ∧ acceptsUnitSq work1261.out = true := by decide +kernel

def cell1261 : CellCertificate where
  tauBall := tau1261
  contactCenter := center1261
  contactBall := contact1261
  work := work1261
  center_sq := center_sq1261
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1261.1
  jac_ok := checks1261.2.1
  accepted := checks1261.2.2

def tau1262 : RatBall :=
  ⟨⟨-109/320, -69/320⟩, 3/640⟩
def center1262 : GaussianRat :=
  ⟨-236668663/1000000000, -134444337/1000000000⟩
def contact1262 : RatBall := localContactBall tau1262 center1262
def work1262 : RoundedTauEval :=
  evalTau precision tau1262 contact1262 logTwoBall

theorem center_sq1262 : (center1262.re : ℝ)^2 +
    (center1262.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1262]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1262 : work1262.theta.ok = true ∧
    work1262.jac.invOK = true ∧ acceptsUnitSq work1262.out = true := by decide +kernel

def cell1262 : CellCertificate where
  tauBall := tau1262
  contactCenter := center1262
  contactBall := contact1262
  work := work1262
  center_sq := center_sq1262
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1262.1
  jac_ok := checks1262.2.1
  accepted := checks1262.2.2

def tau1263 : RatBall :=
  ⟨⟨-107/320, -71/320⟩, 3/640⟩
def center1263 : GaussianRat :=
  ⟨-58317051/250000000, -34747303/250000000⟩
def contact1263 : RatBall := localContactBall tau1263 center1263
def work1263 : RoundedTauEval :=
  evalTau precision tau1263 contact1263 logTwoBall

theorem center_sq1263 : (center1263.re : ℝ)^2 +
    (center1263.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1263]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1263 : work1263.theta.ok = true ∧
    work1263.jac.invOK = true ∧ acceptsUnitSq work1263.out = true := by decide +kernel

def cell1263 : CellCertificate where
  tauBall := tau1263
  contactCenter := center1263
  contactBall := contact1263
  work := work1263
  center_sq := center_sq1263
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1263.1
  jac_ok := checks1263.2.1
  accepted := checks1263.2.2

def cells : List CellCertificate := [cell1256, cell1257, cell1258, cell1259, cell1260, cell1261, cell1262, cell1263]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157


