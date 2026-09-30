-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0309
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0309
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:54.397188+00:00
-- url     : https://prove2.me/theorems/970fe1bb-c16c-4ffc-8257-e05a74d7e246
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0309.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2472 : RatBall :=
  ⟨⟨81/320, 89/320⟩, 3/640⟩
def center2472 : GaussianRat :=
  ⟨92495743/500000000, 184225151/1000000000⟩
def contact2472 : RatBall := localContactBall tau2472 center2472
def work2472 : RoundedTauEval :=
  evalTau precision tau2472 contact2472 logTwoBall

theorem center_sq2472 : (center2472.re : ℝ)^2 +
    (center2472.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2472]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2472 : work2472.theta.ok = true ∧
    work2472.jac.invOK = true ∧ acceptsUnitSq work2472.out = true := by decide +kernel

def cell2472 : CellCertificate where
  tauBall := tau2472
  contactCenter := center2472
  contactBall := contact2472
  work := work2472
  center_sq := center_sq2472
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2472.1
  jac_ok := checks2472.2.1
  accepted := checks2472.2.2

def tau2473 : RatBall :=
  ⟨⟨83/320, 89/320⟩, 3/640⟩
def center2473 : GaussianRat :=
  ⟨189282071/1000000000, 183581561/1000000000⟩
def contact2473 : RatBall := localContactBall tau2473 center2473
def work2473 : RoundedTauEval :=
  evalTau precision tau2473 contact2473 logTwoBall

theorem center_sq2473 : (center2473.re : ℝ)^2 +
    (center2473.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2473]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2473 : work2473.theta.ok = true ∧
    work2473.jac.invOK = true ∧ acceptsUnitSq work2473.out = true := by decide +kernel

def cell2473 : CellCertificate where
  tauBall := tau2473
  contactCenter := center2473
  contactBall := contact2473
  work := work2473
  center_sq := center_sq2473
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2473.1
  jac_ok := checks2473.2.1
  accepted := checks2473.2.2

def tau2474 : RatBall :=
  ⟨⟨81/320, 91/320⟩, 3/640⟩
def center2474 : GaussianRat :=
  ⟨23204849/125000000, 94265223/500000000⟩
def contact2474 : RatBall := localContactBall tau2474 center2474
def work2474 : RoundedTauEval :=
  evalTau precision tau2474 contact2474 logTwoBall

theorem center_sq2474 : (center2474.re : ℝ)^2 +
    (center2474.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2474]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2474 : work2474.theta.ok = true ∧
    work2474.jac.invOK = true ∧ acceptsUnitSq work2474.out = true := by decide +kernel

def cell2474 : CellCertificate where
  tauBall := tau2474
  contactCenter := center2474
  contactBall := contact2474
  work := work2474
  center_sq := center_sq2474
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2474.1
  jac_ok := checks2474.2.1
  accepted := checks2474.2.2

def tau2475 : RatBall :=
  ⟨⟨83/320, 91/320⟩, 3/640⟩
def center2475 : GaussianRat :=
  ⟨37988073/200000000, 37573667/200000000⟩
def contact2475 : RatBall := localContactBall tau2475 center2475
def work2475 : RoundedTauEval :=
  evalTau precision tau2475 contact2475 logTwoBall

theorem center_sq2475 : (center2475.re : ℝ)^2 +
    (center2475.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2475]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2475 : work2475.theta.ok = true ∧
    work2475.jac.invOK = true ∧ acceptsUnitSq work2475.out = true := by decide +kernel

def cell2475 : CellCertificate where
  tauBall := tau2475
  contactCenter := center2475
  contactBall := contact2475
  work := work2475
  center_sq := center_sq2475
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2475.1
  jac_ok := checks2475.2.1
  accepted := checks2475.2.2

def tau2476 : RatBall :=
  ⟨⟨17/64, 89/320⟩, 3/640⟩
def center2476 : GaussianRat :=
  ⟨24194269/125000000, 5716477/31250000⟩
def contact2476 : RatBall := localContactBall tau2476 center2476
def work2476 : RoundedTauEval :=
  evalTau precision tau2476 contact2476 logTwoBall

theorem center_sq2476 : (center2476.re : ℝ)^2 +
    (center2476.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2476]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2476 : work2476.theta.ok = true ∧
    work2476.jac.invOK = true ∧ acceptsUnitSq work2476.out = true := by decide +kernel

def cell2476 : CellCertificate where
  tauBall := tau2476
  contactCenter := center2476
  contactBall := contact2476
  work := work2476
  center_sq := center_sq2476
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2476.1
  jac_ok := checks2476.2.1
  accepted := checks2476.2.2

def tau2477 : RatBall :=
  ⟨⟨87/320, 89/320⟩, 3/640⟩
def center2477 : GaussianRat :=
  ⟨7912299/40000000, 91131277/500000000⟩
def contact2477 : RatBall := localContactBall tau2477 center2477
def work2477 : RoundedTauEval :=
  evalTau precision tau2477 contact2477 logTwoBall

theorem center_sq2477 : (center2477.re : ℝ)^2 +
    (center2477.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2477]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2477 : work2477.theta.ok = true ∧
    work2477.jac.invOK = true ∧ acceptsUnitSq work2477.out = true := by decide +kernel

def cell2477 : CellCertificate where
  tauBall := tau2477
  contactCenter := center2477
  contactBall := contact2477
  work := work2477
  center_sq := center_sq2477
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2477.1
  jac_ok := checks2477.2.1
  accepted := checks2477.2.2

def tau2478 : RatBall :=
  ⟨⟨17/64, 91/320⟩, 3/640⟩
def center2478 : GaussianRat :=
  ⟨97111567/500000000, 37439051/200000000⟩
def contact2478 : RatBall := localContactBall tau2478 center2478
def work2478 : RoundedTauEval :=
  evalTau precision tau2478 contact2478 logTwoBall

theorem center_sq2478 : (center2478.re : ℝ)^2 +
    (center2478.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2478]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2478 : work2478.theta.ok = true ∧
    work2478.jac.invOK = true ∧ acceptsUnitSq work2478.out = true := by decide +kernel

def cell2478 : CellCertificate where
  tauBall := tau2478
  contactCenter := center2478
  contactBall := contact2478
  work := work2478
  center_sq := center_sq2478
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2478.1
  jac_ok := checks2478.2.1
  accepted := checks2478.2.2

def tau2479 : RatBall :=
  ⟨⟨87/320, 91/320⟩, 3/640⟩
def center2479 : GaussianRat :=
  ⟨49621711/250000000, 186511513/1000000000⟩
def contact2479 : RatBall := localContactBall tau2479 center2479
def work2479 : RoundedTauEval :=
  evalTau precision tau2479 contact2479 logTwoBall

theorem center_sq2479 : (center2479.re : ℝ)^2 +
    (center2479.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2479]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2479 : work2479.theta.ok = true ∧
    work2479.jac.invOK = true ∧ acceptsUnitSq work2479.out = true := by decide +kernel

def cell2479 : CellCertificate where
  tauBall := tau2479
  contactCenter := center2479
  contactBall := contact2479
  work := work2479
  center_sq := center_sq2479
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2479.1
  jac_ok := checks2479.2.1
  accepted := checks2479.2.2

def cells : List CellCertificate := [cell2472, cell2473, cell2474, cell2475, cell2476, cell2477, cell2478, cell2479]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309

end


