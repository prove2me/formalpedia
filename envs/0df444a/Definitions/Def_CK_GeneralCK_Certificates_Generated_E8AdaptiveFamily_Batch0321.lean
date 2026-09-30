-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0321
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0321
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:37:31.128381+00:00
-- url     : https://prove2.me/theorems/cf080da9-26f9-4f8e-9512-9bd469a2c5c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0321.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2568 : RatBall :=
  ⟨⟨-27/128, -219/640⟩, 3/1280⟩
def center2568 : GaussianRat :=
  ⟨-162184187/1000000000, -234275597/1000000000⟩
def contact2568 : RatBall := localContactBall tau2568 center2568
def work2568 : RoundedTauEval :=
  evalTau precision tau2568 contact2568 logTwoBall

theorem center_sq2568 : (center2568.re : ℝ)^2 +
    (center2568.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2568]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2568 : work2568.theta.ok = true ∧
    work2568.jac.invOK = true ∧ acceptsUnitSq work2568.out = true := by decide +kernel

def cell2568 : CellCertificate where
  tauBall := tau2568
  contactCenter := center2568
  contactBall := contact2568
  work := work2568
  center_sq := center_sq2568
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2568.1
  jac_ok := checks2568.2.1
  accepted := checks2568.2.2

def tau2569 : RatBall :=
  ⟨⟨-133/640, -219/640⟩, 3/1280⟩
def center2569 : GaussianRat :=
  ⟨-159898033/1000000000, -234643387/1000000000⟩
def contact2569 : RatBall := localContactBall tau2569 center2569
def work2569 : RoundedTauEval :=
  evalTau precision tau2569 contact2569 logTwoBall

theorem center_sq2569 : (center2569.re : ℝ)^2 +
    (center2569.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2569]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2569 : work2569.theta.ok = true ∧
    work2569.jac.invOK = true ∧ acceptsUnitSq work2569.out = true := by decide +kernel

def cell2569 : CellCertificate where
  tauBall := tau2569
  contactCenter := center2569
  contactBall := contact2569
  work := work2569
  center_sq := center_sq2569
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2569.1
  jac_ok := checks2569.2.1
  accepted := checks2569.2.2

def tau2570 : RatBall :=
  ⟨⟨-27/128, -217/640⟩, 3/1280⟩
def center2570 : GaussianRat :=
  ⟨-80908379/500000000, -115996981/500000000⟩
def contact2570 : RatBall := localContactBall tau2570 center2570
def work2570 : RoundedTauEval :=
  evalTau precision tau2570 contact2570 logTwoBall

theorem center_sq2570 : (center2570.re : ℝ)^2 +
    (center2570.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2570]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2570 : work2570.theta.ok = true ∧
    work2570.jac.invOK = true ∧ acceptsUnitSq work2570.out = true := by decide +kernel

def cell2570 : CellCertificate where
  tauBall := tau2570
  contactCenter := center2570
  contactBall := contact2570
  work := work2570
  center_sq := center_sq2570
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2570.1
  jac_ok := checks2570.2.1
  accepted := checks2570.2.2

def tau2571 : RatBall :=
  ⟨⟨-133/640, -217/640⟩, 3/1280⟩
def center2571 : GaussianRat :=
  ⟨-79767381/500000000, -29044611/125000000⟩
def contact2571 : RatBall := localContactBall tau2571 center2571
def work2571 : RoundedTauEval :=
  evalTau precision tau2571 contact2571 logTwoBall

theorem center_sq2571 : (center2571.re : ℝ)^2 +
    (center2571.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2571]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2571 : work2571.theta.ok = true ∧
    work2571.jac.invOK = true ∧ acceptsUnitSq work2571.out = true := by decide +kernel

def cell2571 : CellCertificate where
  tauBall := tau2571
  contactCenter := center2571
  contactBall := contact2571
  work := work2571
  center_sq := center_sq2571
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2571.1
  jac_ok := checks2571.2.1
  accepted := checks2571.2.2

def tau2572 : RatBall :=
  ⟨⟨-131/640, -219/640⟩, 3/1280⟩
def center2572 : GaussianRat :=
  ⟨-157607013/1000000000, -23500697/100000000⟩
def contact2572 : RatBall := localContactBall tau2572 center2572
def work2572 : RoundedTauEval :=
  evalTau precision tau2572 contact2572 logTwoBall

theorem center_sq2572 : (center2572.re : ℝ)^2 +
    (center2572.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2572]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2572 : work2572.theta.ok = true ∧
    work2572.jac.invOK = true ∧ acceptsUnitSq work2572.out = true := by decide +kernel

def cell2572 : CellCertificate where
  tauBall := tau2572
  contactCenter := center2572
  contactBall := contact2572
  work := work2572
  center_sq := center_sq2572
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2572.1
  jac_ok := checks2572.2.1
  accepted := checks2572.2.2

def tau2573 : RatBall :=
  ⟨⟨-129/640, -219/640⟩, 3/1280⟩
def center2573 : GaussianRat :=
  ⟨-155311177/1000000000, -29420787/125000000⟩
def contact2573 : RatBall := localContactBall tau2573 center2573
def work2573 : RoundedTauEval :=
  evalTau precision tau2573 contact2573 logTwoBall

theorem center_sq2573 : (center2573.re : ℝ)^2 +
    (center2573.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2573]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2573 : work2573.theta.ok = true ∧
    work2573.jac.invOK = true ∧ acceptsUnitSq work2573.out = true := by decide +kernel

def cell2573 : CellCertificate where
  tauBall := tau2573
  contactCenter := center2573
  contactBall := contact2573
  work := work2573
  center_sq := center_sq2573
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2573.1
  jac_ok := checks2573.2.1
  accepted := checks2573.2.2

def tau2574 : RatBall :=
  ⟨⟨-131/640, -217/640⟩, 3/1280⟩
def center2574 : GaussianRat :=
  ⟨-157247951/1000000000, -46543131/200000000⟩
def contact2574 : RatBall := localContactBall tau2574 center2574
def work2574 : RoundedTauEval :=
  evalTau precision tau2574 contact2574 logTwoBall

theorem center_sq2574 : (center2574.re : ℝ)^2 +
    (center2574.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2574]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2574 : work2574.theta.ok = true ∧
    work2574.jac.invOK = true ∧ acceptsUnitSq work2574.out = true := by decide +kernel

def cell2574 : CellCertificate where
  tauBall := tau2574
  contactCenter := center2574
  contactBall := contact2574
  work := work2574
  center_sq := center_sq2574
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2574.1
  jac_ok := checks2574.2.1
  accepted := checks2574.2.2

def tau2575 : RatBall :=
  ⟨⟨-129/640, -217/640⟩, 3/1280⟩
def center2575 : GaussianRat :=
  ⟨-38739093/250000000, -233070213/1000000000⟩
def contact2575 : RatBall := localContactBall tau2575 center2575
def work2575 : RoundedTauEval :=
  evalTau precision tau2575 contact2575 logTwoBall

theorem center_sq2575 : (center2575.re : ℝ)^2 +
    (center2575.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2575]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2575 : work2575.theta.ok = true ∧
    work2575.jac.invOK = true ∧ acceptsUnitSq work2575.out = true := by decide +kernel

def cell2575 : CellCertificate where
  tauBall := tau2575
  contactCenter := center2575
  contactBall := contact2575
  work := work2575
  center_sq := center_sq2575
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2575.1
  jac_ok := checks2575.2.1
  accepted := checks2575.2.2

def cells : List CellCertificate := [cell2568, cell2569, cell2570, cell2571, cell2572, cell2573, cell2574, cell2575]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321

end


