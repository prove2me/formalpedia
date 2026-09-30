-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0331
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0331
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:11.198531+00:00
-- url     : https://prove2.me/theorems/78820cbd-c630-4d1b-89bb-3c283db92c1f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0331.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2648 : RatBall :=
  ⟨⟨-69/640, -49/128⟩, 3/1280⟩
def center2648 : GaussianRat :=
  ⟨-43712483/500000000, -34478141/125000000⟩
def contact2648 : RatBall := localContactBall tau2648 center2648
def work2648 : RoundedTauEval :=
  evalTau precision tau2648 contact2648 logTwoBall

theorem center_sq2648 : (center2648.re : ℝ)^2 +
    (center2648.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2648]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2648 : work2648.theta.ok = true ∧
    work2648.jac.invOK = true ∧ acceptsUnitSq work2648.out = true := by decide +kernel

def cell2648 : CellCertificate where
  tauBall := tau2648
  contactCenter := center2648
  contactBall := contact2648
  work := work2648
  center_sq := center_sq2648
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2648.1
  jac_ok := checks2648.2.1
  accepted := checks2648.2.2

def tau2649 : RatBall :=
  ⟨⟨-67/640, -247/640⟩, 3/1280⟩
def center2649 : GaussianRat :=
  ⟨-42585897/500000000, -278570563/1000000000⟩
def contact2649 : RatBall := localContactBall tau2649 center2649
def work2649 : RoundedTauEval :=
  evalTau precision tau2649 contact2649 logTwoBall

theorem center_sq2649 : (center2649.re : ℝ)^2 +
    (center2649.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2649]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2649 : work2649.theta.ok = true ∧
    work2649.jac.invOK = true ∧ acceptsUnitSq work2649.out = true := by decide +kernel

def cell2649 : CellCertificate where
  tauBall := tau2649
  contactCenter := center2649
  contactBall := contact2649
  work := work2649
  center_sq := center_sq2649
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2649.1
  jac_ok := checks2649.2.1
  accepted := checks2649.2.2

def tau2650 : RatBall :=
  ⟨⟨-13/128, -247/640⟩, 3/1280⟩
def center2650 : GaussianRat :=
  ⟨-82665793/1000000000, -278811601/1000000000⟩
def contact2650 : RatBall := localContactBall tau2650 center2650
def work2650 : RoundedTauEval :=
  evalTau precision tau2650 contact2650 logTwoBall

theorem center_sq2650 : (center2650.re : ℝ)^2 +
    (center2650.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2650]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2650 : work2650.theta.ok = true ∧
    work2650.jac.invOK = true ∧ acceptsUnitSq work2650.out = true := by decide +kernel

def cell2650 : CellCertificate where
  tauBall := tau2650
  contactCenter := center2650
  contactBall := contact2650
  work := work2650
  center_sq := center_sq2650
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2650.1
  jac_ok := checks2650.2.1
  accepted := checks2650.2.2

def tau2651 : RatBall :=
  ⟨⟨-67/640, -49/128⟩, 3/1280⟩
def center2651 : GaussianRat :=
  ⟨-42464509/500000000, -34508699/125000000⟩
def contact2651 : RatBall := localContactBall tau2651 center2651
def work2651 : RoundedTauEval :=
  evalTau precision tau2651 contact2651 logTwoBall

theorem center_sq2651 : (center2651.re : ℝ)^2 +
    (center2651.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2651]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2651 : work2651.theta.ok = true ∧
    work2651.jac.invOK = true ∧ acceptsUnitSq work2651.out = true := by decide +kernel

def cell2651 : CellCertificate where
  tauBall := tau2651
  contactCenter := center2651
  contactBall := contact2651
  work := work2651
  center_sq := center_sq2651
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2651.1
  jac_ok := checks2651.2.1
  accepted := checks2651.2.2

def tau2652 : RatBall :=
  ⟨⟨-13/128, -49/128⟩, 3/1280⟩
def center2652 : GaussianRat :=
  ⟨-41214889/500000000, -1726921/6250000⟩
def contact2652 : RatBall := localContactBall tau2652 center2652
def work2652 : RoundedTauEval :=
  evalTau precision tau2652 contact2652 logTwoBall

theorem center_sq2652 : (center2652.re : ℝ)^2 +
    (center2652.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2652]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2652 : work2652.theta.ok = true ∧
    work2652.jac.invOK = true ∧ acceptsUnitSq work2652.out = true := by decide +kernel

def cell2652 : CellCertificate where
  tauBall := tau2652
  contactCenter := center2652
  contactBall := contact2652
  work := work2652
  center_sq := center_sq2652
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2652.1
  jac_ok := checks2652.2.1
  accepted := checks2652.2.2

def tau2653 : RatBall :=
  ⟨⟨-71/640, -243/640⟩, 3/1280⟩
def center2653 : GaussianRat :=
  ⟨-89664833/1000000000, -68271613/250000000⟩
def contact2653 : RatBall := localContactBall tau2653 center2653
def work2653 : RoundedTauEval :=
  evalTau precision tau2653 contact2653 logTwoBall

theorem center_sq2653 : (center2653.re : ℝ)^2 +
    (center2653.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2653]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2653 : work2653.theta.ok = true ∧
    work2653.jac.invOK = true ∧ acceptsUnitSq work2653.out = true := by decide +kernel

def cell2653 : CellCertificate where
  tauBall := tau2653
  contactCenter := center2653
  contactBall := contact2653
  work := work2653
  center_sq := center_sq2653
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2653.1
  jac_ok := checks2653.2.1
  accepted := checks2653.2.2

def tau2654 : RatBall :=
  ⟨⟨-69/640, -243/640⟩, 3/1280⟩
def center2654 : GaussianRat :=
  ⟨-87178851/1000000000, -273334167/1000000000⟩
def contact2654 : RatBall := localContactBall tau2654 center2654
def work2654 : RoundedTauEval :=
  evalTau precision tau2654 contact2654 logTwoBall

theorem center_sq2654 : (center2654.re : ℝ)^2 +
    (center2654.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2654]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2654 : work2654.theta.ok = true ∧
    work2654.jac.invOK = true ∧ acceptsUnitSq work2654.out = true := by decide +kernel

def cell2654 : CellCertificate where
  tauBall := tau2654
  contactCenter := center2654
  contactBall := contact2654
  work := work2654
  center_sq := center_sq2654
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2654.1
  jac_ok := checks2654.2.1
  accepted := checks2654.2.2

def tau2655 : RatBall :=
  ⟨⟨-71/640, -241/640⟩, 3/1280⟩
def center2655 : GaussianRat :=
  ⟨-89415553/1000000000, -270605413/1000000000⟩
def contact2655 : RatBall := localContactBall tau2655 center2655
def work2655 : RoundedTauEval :=
  evalTau precision tau2655 contact2655 logTwoBall

theorem center_sq2655 : (center2655.re : ℝ)^2 +
    (center2655.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2655]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2655 : work2655.theta.ok = true ∧
    work2655.jac.invOK = true ∧ acceptsUnitSq work2655.out = true := by decide +kernel

def cell2655 : CellCertificate where
  tauBall := tau2655
  contactCenter := center2655
  contactBall := contact2655
  work := work2655
  center_sq := center_sq2655
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2655.1
  jac_ok := checks2655.2.1
  accepted := checks2655.2.2

def cells : List CellCertificate := [cell2648, cell2649, cell2650, cell2651, cell2652, cell2653, cell2654, cell2655]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331

end


