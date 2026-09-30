-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0326
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0326
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:08:17.338483+00:00
-- url     : https://prove2.me/theorems/2182a44f-b5f4-4b1a-8094-8277b891cca5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0326.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2608 : RatBall :=
  ⟨⟨-109/640, -231/640⟩, 3/1280⟩
def center2608 : GaussianRat :=
  ⟨-134046881/1000000000, -15803901/62500000⟩
def contact2608 : RatBall := localContactBall tau2608 center2608
def work2608 : RoundedTauEval :=
  evalTau precision tau2608 contact2608 logTwoBall

theorem center_sq2608 : (center2608.re : ℝ)^2 +
    (center2608.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2608]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2608 : work2608.theta.ok = true ∧
    work2608.jac.invOK = true ∧ acceptsUnitSq work2608.out = true := by decide +kernel

def cell2608 : CellCertificate where
  tauBall := tau2608
  contactCenter := center2608
  contactBall := contact2608
  work := work2608
  center_sq := center_sq2608
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2608.1
  jac_ok := checks2608.2.1
  accepted := checks2608.2.2

def tau2609 : RatBall :=
  ⟨⟨-111/640, -229/640⟩, 3/1280⟩
def center2609 : GaussianRat :=
  ⟨-136076987/1000000000, -250155999/1000000000⟩
def contact2609 : RatBall := localContactBall tau2609 center2609
def work2609 : RoundedTauEval :=
  evalTau precision tau2609 contact2609 logTwoBall

theorem center_sq2609 : (center2609.re : ℝ)^2 +
    (center2609.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2609]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2609 : work2609.theta.ok = true ∧
    work2609.jac.invOK = true ∧ acceptsUnitSq work2609.out = true := by decide +kernel

def cell2609 : CellCertificate where
  tauBall := tau2609
  contactCenter := center2609
  contactBall := contact2609
  work := work2609
  center_sq := center_sq2609
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2609.1
  jac_ok := checks2609.2.1
  accepted := checks2609.2.2

def tau2610 : RatBall :=
  ⟨⟨-109/640, -229/640⟩, 3/1280⟩
def center2610 : GaussianRat :=
  ⟨-133711273/1000000000, -250491903/1000000000⟩
def contact2610 : RatBall := localContactBall tau2610 center2610
def work2610 : RoundedTauEval :=
  evalTau precision tau2610 contact2610 logTwoBall

theorem center_sq2610 : (center2610.re : ℝ)^2 +
    (center2610.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2610]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2610 : work2610.theta.ok = true ∧
    work2610.jac.invOK = true ∧ acceptsUnitSq work2610.out = true := by decide +kernel

def cell2610 : CellCertificate where
  tauBall := tau2610
  contactCenter := center2610
  contactBall := contact2610
  work := work2610
  center_sq := center_sq2610
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2610.1
  jac_ok := checks2610.2.1
  accepted := checks2610.2.2

def tau2611 : RatBall :=
  ⟨⟨-107/640, -231/640⟩, 3/1280⟩
def center2611 : GaussianRat :=
  ⟨-65835777/500000000, -253197689/1000000000⟩
def contact2611 : RatBall := localContactBall tau2611 center2611
def work2611 : RoundedTauEval :=
  evalTau precision tau2611 contact2611 logTwoBall

theorem center_sq2611 : (center2611.re : ℝ)^2 +
    (center2611.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2611]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2611 : work2611.theta.ok = true ∧
    work2611.jac.invOK = true ∧ acceptsUnitSq work2611.out = true := by decide +kernel

def cell2611 : CellCertificate where
  tauBall := tau2611
  contactCenter := center2611
  contactBall := contact2611
  work := work2611
  center_sq := center_sq2611
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2611.1
  jac_ok := checks2611.2.1
  accepted := checks2611.2.2

def tau2612 : RatBall :=
  ⟨⟨-21/128, -231/640⟩, 3/1280⟩
def center2612 : GaussianRat :=
  ⟨-32322943/250000000, -63381939/250000000⟩
def contact2612 : RatBall := localContactBall tau2612 center2612
def work2612 : RoundedTauEval :=
  evalTau precision tau2612 contact2612 logTwoBall

theorem center_sq2612 : (center2612.re : ℝ)^2 +
    (center2612.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2612]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2612 : work2612.theta.ok = true ∧
    work2612.jac.invOK = true ∧ acceptsUnitSq work2612.out = true := by decide +kernel

def cell2612 : CellCertificate where
  tauBall := tau2612
  contactCenter := center2612
  contactBall := contact2612
  work := work2612
  center_sq := center_sq2612
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2612.1
  jac_ok := checks2612.2.1
  accepted := checks2612.2.2

def tau2613 : RatBall :=
  ⟨⟨-107/640, -229/640⟩, 3/1280⟩
def center2613 : GaussianRat :=
  ⟨-65670547/500000000, -62705679/250000000⟩
def contact2613 : RatBall := localContactBall tau2613 center2613
def work2613 : RoundedTauEval :=
  evalTau precision tau2613 contact2613 logTwoBall

theorem center_sq2613 : (center2613.re : ℝ)^2 +
    (center2613.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2613]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2613 : work2613.theta.ok = true ∧
    work2613.jac.invOK = true ∧ acceptsUnitSq work2613.out = true := by decide +kernel

def cell2613 : CellCertificate where
  tauBall := tau2613
  contactCenter := center2613
  contactBall := contact2613
  work := work2613
  center_sq := center_sq2613
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2613.1
  jac_ok := checks2613.2.1
  accepted := checks2613.2.2

def tau2614 : RatBall :=
  ⟨⟨-21/128, -229/640⟩, 3/1280⟩
def center2614 : GaussianRat :=
  ⟨-128966511/1000000000, -50229677/200000000⟩
def contact2614 : RatBall := localContactBall tau2614 center2614
def work2614 : RoundedTauEval :=
  evalTau precision tau2614 contact2614 logTwoBall

theorem center_sq2614 : (center2614.re : ℝ)^2 +
    (center2614.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2614]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2614 : work2614.theta.ok = true ∧
    work2614.jac.invOK = true ∧ acceptsUnitSq work2614.out = true := by decide +kernel

def cell2614 : CellCertificate where
  tauBall := tau2614
  contactCenter := center2614
  contactBall := contact2614
  work := work2614
  center_sq := center_sq2614
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2614.1
  jac_ok := checks2614.2.1
  accepted := checks2614.2.2

def tau2615 : RatBall :=
  ⟨⟨-111/640, -227/640⟩, 3/1280⟩
def center2615 : GaussianRat :=
  ⟨-135740809/1000000000, -4955901/20000000⟩
def contact2615 : RatBall := localContactBall tau2615 center2615
def work2615 : RoundedTauEval :=
  evalTau precision tau2615 contact2615 logTwoBall

theorem center_sq2615 : (center2615.re : ℝ)^2 +
    (center2615.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2615]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2615 : work2615.theta.ok = true ∧
    work2615.jac.invOK = true ∧ acceptsUnitSq work2615.out = true := by decide +kernel

def cell2615 : CellCertificate where
  tauBall := tau2615
  contactCenter := center2615
  contactBall := contact2615
  work := work2615
  center_sq := center_sq2615
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2615.1
  jac_ok := checks2615.2.1
  accepted := checks2615.2.2

def cells : List CellCertificate := [cell2608, cell2609, cell2610, cell2611, cell2612, cell2613, cell2614, cell2615]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326

end


