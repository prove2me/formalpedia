-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0308
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0308
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:12:56.399872+00:00
-- url     : https://prove2.me/theorems/1344c9bc-b9ec-4ccf-a63d-68b6d5a2ce97
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0308.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2464 : RatBall :=
  ⟨⟨89/320, 17/64⟩, 3/640⟩
def center2464 : GaussianRat :=
  ⟨20072031/100000000, 86578791/500000000⟩
def contact2464 : RatBall := localContactBall tau2464 center2464
def work2464 : RoundedTauEval :=
  evalTau precision tau2464 contact2464 logTwoBall

theorem center_sq2464 : (center2464.re : ℝ)^2 +
    (center2464.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2464]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2464 : work2464.theta.ok = true ∧
    work2464.jac.invOK = true ∧ acceptsUnitSq work2464.out = true := by decide +kernel

def cell2464 : CellCertificate where
  tauBall := tau2464
  contactCenter := center2464
  contactBall := contact2464
  work := work2464
  center_sq := center_sq2464
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2464.1
  jac_ok := checks2464.2.1
  accepted := checks2464.2.2

def tau2465 : RatBall :=
  ⟨⟨91/320, 17/64⟩, 3/640⟩
def center2465 : GaussianRat :=
  ⟨102458249/500000000, 172511057/1000000000⟩
def contact2465 : RatBall := localContactBall tau2465 center2465
def work2465 : RoundedTauEval :=
  evalTau precision tau2465 contact2465 logTwoBall

theorem center_sq2465 : (center2465.re : ℝ)^2 +
    (center2465.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2465]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2465 : work2465.theta.ok = true ∧
    work2465.jac.invOK = true ∧ acceptsUnitSq work2465.out = true := by decide +kernel

def cell2465 : CellCertificate where
  tauBall := tau2465
  contactCenter := center2465
  contactBall := contact2465
  work := work2465
  center_sq := center_sq2465
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2465.1
  jac_ok := checks2465.2.1
  accepted := checks2465.2.2

def tau2466 : RatBall :=
  ⟨⟨89/320, 87/320⟩, 3/640⟩
def center2466 : GaussianRat :=
  ⟨201371579/1000000000, 177367859/1000000000⟩
def contact2466 : RatBall := localContactBall tau2466 center2466
def work2466 : RoundedTauEval :=
  evalTau precision tau2466 contact2466 logTwoBall

theorem center_sq2466 : (center2466.re : ℝ)^2 +
    (center2466.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2466]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2466 : work2466.theta.ok = true ∧
    work2466.jac.invOK = true ∧ acceptsUnitSq work2466.out = true := by decide +kernel

def cell2466 : CellCertificate where
  tauBall := tau2466
  contactCenter := center2466
  contactBall := contact2466
  work := work2466
  center_sq := center_sq2466
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2466.1
  jac_ok := checks2466.2.1
  accepted := checks2466.2.2

def tau2467 : RatBall :=
  ⟨⟨91/320, 87/320⟩, 3/640⟩
def center2467 : GaussianRat :=
  ⟨102788551/500000000, 176702417/1000000000⟩
def contact2467 : RatBall := localContactBall tau2467 center2467
def work2467 : RoundedTauEval :=
  evalTau precision tau2467 contact2467 logTwoBall

theorem center_sq2467 : (center2467.re : ℝ)^2 +
    (center2467.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2467]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2467 : work2467.theta.ok = true ∧
    work2467.jac.invOK = true ∧ acceptsUnitSq work2467.out = true := by decide +kernel

def cell2467 : CellCertificate where
  tauBall := tau2467
  contactCenter := center2467
  contactBall := contact2467
  work := work2467
  center_sq := center_sq2467
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2467.1
  jac_ok := checks2467.2.1
  accepted := checks2467.2.2

def tau2468 : RatBall :=
  ⟨⟨93/320, 17/64⟩, 3/640⟩
def center2468 : GaussianRat :=
  ⟨104546899/500000000, 171855447/1000000000⟩
def contact2468 : RatBall := localContactBall tau2468 center2468
def work2468 : RoundedTauEval :=
  evalTau precision tau2468 contact2468 logTwoBall

theorem center_sq2468 : (center2468.re : ℝ)^2 +
    (center2468.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2468]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2468 : work2468.theta.ok = true ∧
    work2468.jac.invOK = true ∧ acceptsUnitSq work2468.out = true := by decide +kernel

def cell2468 : CellCertificate where
  tauBall := tau2468
  contactCenter := center2468
  contactBall := contact2468
  work := work2468
  center_sq := center_sq2468
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2468.1
  jac_ok := checks2468.2.1
  accepted := checks2468.2.2

def tau2469 : RatBall :=
  ⟨⟨19/64, 17/64⟩, 3/640⟩
def center2469 : GaussianRat :=
  ⟨42650399/200000000, 171191029/1000000000⟩
def contact2469 : RatBall := localContactBall tau2469 center2469
def work2469 : RoundedTauEval :=
  evalTau precision tau2469 contact2469 logTwoBall

theorem center_sq2469 : (center2469.re : ℝ)^2 +
    (center2469.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2469]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2469 : work2469.theta.ok = true ∧
    work2469.jac.invOK = true ∧ acceptsUnitSq work2469.out = true := by decide +kernel

def cell2469 : CellCertificate where
  tauBall := tau2469
  contactCenter := center2469
  contactBall := contact2469
  work := work2469
  center_sq := center_sq2469
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2469.1
  jac_ok := checks2469.2.1
  accepted := checks2469.2.2

def tau2470 : RatBall :=
  ⟨⟨93/320, 87/320⟩, 3/640⟩
def center2470 : GaussianRat :=
  ⟨1638777/7812500, 17602767/100000000⟩
def contact2470 : RatBall := localContactBall tau2470 center2470
def work2470 : RoundedTauEval :=
  evalTau precision tau2470 contact2470 logTwoBall

theorem center_sq2470 : (center2470.re : ℝ)^2 +
    (center2470.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2470]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2470 : work2470.theta.ok = true ∧
    work2470.jac.invOK = true ∧ acceptsUnitSq work2470.out = true := by decide +kernel

def cell2470 : CellCertificate where
  tauBall := tau2470
  contactCenter := center2470
  contactBall := contact2470
  work := work2470
  center_sq := center_sq2470
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2470.1
  jac_ok := checks2470.2.1
  accepted := checks2470.2.2

def tau2471 : RatBall :=
  ⟨⟨19/64, 87/320⟩, 3/640⟩
def center2471 : GaussianRat :=
  ⟨106965213/500000000, 35068781/200000000⟩
def contact2471 : RatBall := localContactBall tau2471 center2471
def work2471 : RoundedTauEval :=
  evalTau precision tau2471 contact2471 logTwoBall

theorem center_sq2471 : (center2471.re : ℝ)^2 +
    (center2471.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2471]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2471 : work2471.theta.ok = true ∧
    work2471.jac.invOK = true ∧ acceptsUnitSq work2471.out = true := by decide +kernel

def cell2471 : CellCertificate where
  tauBall := tau2471
  contactCenter := center2471
  contactBall := contact2471
  work := work2471
  center_sq := center_sq2471
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2471.1
  jac_ok := checks2471.2.1
  accepted := checks2471.2.2

def cells : List CellCertificate := [cell2464, cell2465, cell2466, cell2467, cell2468, cell2469, cell2470, cell2471]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308

end


