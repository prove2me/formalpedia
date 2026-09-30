-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0314
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0314
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:03:42.864409+00:00
-- url     : https://prove2.me/theorems/5de13920-ef9f-46e4-98bc-9ad3c5b18104
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0314.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2512 : RatBall :=
  ⟨⟨101/320, 79/320⟩, 3/640⟩
def center2512 : GaussianRat :=
  ⟨111809453/500000000, 156912213/1000000000⟩
def contact2512 : RatBall := localContactBall tau2512 center2512
def work2512 : RoundedTauEval :=
  evalTau precision tau2512 contact2512 logTwoBall

theorem center_sq2512 : (center2512.re : ℝ)^2 +
    (center2512.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2512]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2512 : work2512.theta.ok = true ∧
    work2512.jac.invOK = true ∧ acceptsUnitSq work2512.out = true := by decide +kernel

def cell2512 : CellCertificate where
  tauBall := tau2512
  contactCenter := center2512
  contactBall := contact2512
  work := work2512
  center_sq := center_sq2512
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2512.1
  jac_ok := checks2512.2.1
  accepted := checks2512.2.2

def tau2513 : RatBall :=
  ⟨⟨21/64, 73/320⟩, 3/640⟩
def center2513 : GaussianRat :=
  ⟨229856067/1000000000, 5742857/40000000⟩
def contact2513 : RatBall := localContactBall tau2513 center2513
def work2513 : RoundedTauEval :=
  evalTau precision tau2513 contact2513 logTwoBall

theorem center_sq2513 : (center2513.re : ℝ)^2 +
    (center2513.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2513]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2513 : work2513.theta.ok = true ∧
    work2513.jac.invOK = true ∧ acceptsUnitSq work2513.out = true := by decide +kernel

def cell2513 : CellCertificate where
  tauBall := tau2513
  contactCenter := center2513
  contactBall := contact2513
  work := work2513
  center_sq := center_sq2513
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2513.1
  jac_ok := checks2513.2.1
  accepted := checks2513.2.2

def tau2514 : RatBall :=
  ⟨⟨21/64, 15/64⟩, 3/640⟩
def center2514 : GaussianRat :=
  ⟨14403551/62500000, 14758413/100000000⟩
def contact2514 : RatBall := localContactBall tau2514 center2514
def work2514 : RoundedTauEval :=
  evalTau precision tau2514 contact2514 logTwoBall

theorem center_sq2514 : (center2514.re : ℝ)^2 +
    (center2514.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2514]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2514 : work2514.theta.ok = true ∧
    work2514.jac.invOK = true ∧ acceptsUnitSq work2514.out = true := by decide +kernel

def cell2514 : CellCertificate where
  tauBall := tau2514
  contactCenter := center2514
  contactBall := contact2514
  work := work2514
  center_sq := center_sq2514
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2514.1
  jac_ok := checks2514.2.1
  accepted := checks2514.2.2

def tau2515 : RatBall :=
  ⟨⟨97/320, 81/320⟩, 3/640⟩
def center2515 : GaussianRat :=
  ⟨108037641/500000000, 81137999/500000000⟩
def contact2515 : RatBall := localContactBall tau2515 center2515
def work2515 : RoundedTauEval :=
  evalTau precision tau2515 contact2515 logTwoBall

theorem center_sq2515 : (center2515.re : ℝ)^2 +
    (center2515.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2515]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2515 : work2515.theta.ok = true ∧
    work2515.jac.invOK = true ∧ acceptsUnitSq work2515.out = true := by decide +kernel

def cell2515 : CellCertificate where
  tauBall := tau2515
  contactCenter := center2515
  contactBall := contact2515
  work := work2515
  center_sq := center_sq2515
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2515.1
  jac_ok := checks2515.2.1
  accepted := checks2515.2.2

def tau2516 : RatBall :=
  ⟨⟨99/320, 81/320⟩, 3/640⟩
def center2516 : GaussianRat :=
  ⟨55044701/250000000, 161633449/1000000000⟩
def contact2516 : RatBall := localContactBall tau2516 center2516
def work2516 : RoundedTauEval :=
  evalTau precision tau2516 contact2516 logTwoBall

theorem center_sq2516 : (center2516.re : ℝ)^2 +
    (center2516.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2516]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2516 : work2516.theta.ok = true ∧
    work2516.jac.invOK = true ∧ acceptsUnitSq work2516.out = true := by decide +kernel

def cell2516 : CellCertificate where
  tauBall := tau2516
  contactCenter := center2516
  contactBall := contact2516
  work := work2516
  center_sq := center_sq2516
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2516.1
  jac_ok := checks2516.2.1
  accepted := checks2516.2.2

def tau2517 : RatBall :=
  ⟨⟨97/320, 83/320⟩, 3/640⟩
def center2517 : GaussianRat :=
  ⟨108361733/500000000, 83196503/500000000⟩
def contact2517 : RatBall := localContactBall tau2517 center2517
def work2517 : RoundedTauEval :=
  evalTau precision tau2517 contact2517 logTwoBall

theorem center_sq2517 : (center2517.re : ℝ)^2 +
    (center2517.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2517]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2517 : work2517.theta.ok = true ∧
    work2517.jac.invOK = true ∧ acceptsUnitSq work2517.out = true := by decide +kernel

def cell2517 : CellCertificate where
  tauBall := tau2517
  contactCenter := center2517
  contactBall := contact2517
  work := work2517
  center_sq := center_sq2517
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2517.1
  jac_ok := checks2517.2.1
  accepted := checks2517.2.2

def tau2518 : RatBall :=
  ⟨⟨99/320, 83/320⟩, 3/640⟩
def center2518 : GaussianRat :=
  ⟨110417413/500000000, 165731261/1000000000⟩
def contact2518 : RatBall := localContactBall tau2518 center2518
def work2518 : RoundedTauEval :=
  evalTau precision tau2518 contact2518 logTwoBall

theorem center_sq2518 : (center2518.re : ℝ)^2 +
    (center2518.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2518]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2518 : work2518.theta.ok = true ∧
    work2518.jac.invOK = true ∧ acceptsUnitSq work2518.out = true := by decide +kernel

def cell2518 : CellCertificate where
  tauBall := tau2518
  contactCenter := center2518
  contactBall := contact2518
  work := work2518
  center_sq := center_sq2518
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2518.1
  jac_ok := checks2518.2.1
  accepted := checks2518.2.2

def tau2519 : RatBall :=
  ⟨⟨97/320, 17/64⟩, 3/640⟩
def center2519 : GaussianRat :=
  ⟨54347721/250000000, 170518079/1000000000⟩
def contact2519 : RatBall := localContactBall tau2519 center2519
def work2519 : RoundedTauEval :=
  evalTau precision tau2519 contact2519 logTwoBall

theorem center_sq2519 : (center2519.re : ℝ)^2 +
    (center2519.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2519]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2519 : work2519.theta.ok = true ∧
    work2519.jac.invOK = true ∧ acceptsUnitSq work2519.out = true := by decide +kernel

def cell2519 : CellCertificate where
  tauBall := tau2519
  contactCenter := center2519
  contactBall := contact2519
  work := work2519
  center_sq := center_sq2519
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2519.1
  jac_ok := checks2519.2.1
  accepted := checks2519.2.2

def cells : List CellCertificate := [cell2512, cell2513, cell2514, cell2515, cell2516, cell2517, cell2518, cell2519]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314

end


