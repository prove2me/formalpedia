-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0330
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0330
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:53:18.353212+00:00
-- url     : https://prove2.me/theorems/d44b9fef-10ee-4c94-8164-bcf26ac77f1e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0330.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2640 : RatBall :=
  ⟨⟨-77/640, -241/640⟩, 3/1280⟩
def center2640 : GaussianRat :=
  ⟨-96833401/1000000000, -8432309/31250000⟩
def contact2640 : RatBall := localContactBall tau2640 center2640
def work2640 : RoundedTauEval :=
  evalTau precision tau2640 contact2640 logTwoBall

theorem center_sq2640 : (center2640.re : ℝ)^2 +
    (center2640.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2640]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2640 : work2640.theta.ok = true ∧
    work2640.jac.invOK = true ∧ acceptsUnitSq work2640.out = true := by decide +kernel

def cell2640 : CellCertificate where
  tauBall := tau2640
  contactCenter := center2640
  contactBall := contact2640
  work := work2640
  center_sq := center_sq2640
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2640.1
  jac_ok := checks2640.2.1
  accepted := checks2640.2.2

def tau2641 : RatBall :=
  ⟨⟨-15/128, -243/640⟩, 3/1280⟩
def center2641 : GaussianRat :=
  ⟨-94626451/1000000000, -272571501/1000000000⟩
def contact2641 : RatBall := localContactBall tau2641 center2641
def work2641 : RoundedTauEval :=
  evalTau precision tau2641 contact2641 logTwoBall

theorem center_sq2641 : (center2641.re : ℝ)^2 +
    (center2641.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2641]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2641 : work2641.theta.ok = true ∧
    work2641.jac.invOK = true ∧ acceptsUnitSq work2641.out = true := by decide +kernel

def cell2641 : CellCertificate where
  tauBall := tau2641
  contactCenter := center2641
  contactBall := contact2641
  work := work2641
  center_sq := center_sq2641
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2641.1
  jac_ok := checks2641.2.1
  accepted := checks2641.2.2

def tau2642 : RatBall :=
  ⟨⟨-73/640, -243/640⟩, 3/1280⟩
def center2642 : GaussianRat :=
  ⟨-46073697/500000000, -54566443/200000000⟩
def contact2642 : RatBall := localContactBall tau2642 center2642
def work2642 : RoundedTauEval :=
  evalTau precision tau2642 contact2642 logTwoBall

theorem center_sq2642 : (center2642.re : ℝ)^2 +
    (center2642.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2642]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2642 : work2642.theta.ok = true ∧
    work2642.jac.invOK = true ∧ acceptsUnitSq work2642.out = true := by decide +kernel

def cell2642 : CellCertificate where
  tauBall := tau2642
  contactCenter := center2642
  contactBall := contact2642
  work := work2642
  center_sq := center_sq2642
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2642.1
  jac_ok := checks2642.2.1
  accepted := checks2642.2.2

def tau2643 : RatBall :=
  ⟨⟨-15/128, -241/640⟩, 3/1280⟩
def center2643 : GaussianRat :=
  ⟨-943643/10000000, -270097427/1000000000⟩
def contact2643 : RatBall := localContactBall tau2643 center2643
def work2643 : RoundedTauEval :=
  evalTau precision tau2643 contact2643 logTwoBall

theorem center_sq2643 : (center2643.re : ℝ)^2 +
    (center2643.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2643]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2643 : work2643.theta.ok = true ∧
    work2643.jac.invOK = true ∧ acceptsUnitSq work2643.out = true := by decide +kernel

def cell2643 : CellCertificate where
  tauBall := tau2643
  contactCenter := center2643
  contactBall := contact2643
  work := work2643
  center_sq := center_sq2643
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2643.1
  jac_ok := checks2643.2.1
  accepted := checks2643.2.2

def tau2644 : RatBall :=
  ⟨⟨-73/640, -241/640⟩, 3/1280⟩
def center2644 : GaussianRat :=
  ⟨-11486457/125000000, -270354617/1000000000⟩
def contact2644 : RatBall := localContactBall tau2644 center2644
def work2644 : RoundedTauEval :=
  evalTau precision tau2644 contact2644 logTwoBall

theorem center_sq2644 : (center2644.re : ℝ)^2 +
    (center2644.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2644 : work2644.theta.ok = true ∧
    work2644.jac.invOK = true ∧ acceptsUnitSq work2644.out = true := by decide +kernel

def cell2644 : CellCertificate where
  tauBall := tau2644
  contactCenter := center2644
  contactBall := contact2644
  work := work2644
  center_sq := center_sq2644
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2644.1
  jac_ok := checks2644.2.1
  accepted := checks2644.2.2

def tau2645 : RatBall :=
  ⟨⟨-71/640, -247/640⟩, 3/1280⟩
def center2645 : GaussianRat :=
  ⟨-90173701/1000000000, -278068181/1000000000⟩
def contact2645 : RatBall := localContactBall tau2645 center2645
def work2645 : RoundedTauEval :=
  evalTau precision tau2645 contact2645 logTwoBall

theorem center_sq2645 : (center2645.re : ℝ)^2 +
    (center2645.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2645]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2645 : work2645.theta.ok = true ∧
    work2645.jac.invOK = true ∧ acceptsUnitSq work2645.out = true := by decide +kernel

def cell2645 : CellCertificate where
  tauBall := tau2645
  contactCenter := center2645
  contactBall := contact2645
  work := work2645
  center_sq := center_sq2645
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2645.1
  jac_ok := checks2645.2.1
  accepted := checks2645.2.2

def tau2646 : RatBall :=
  ⟨⟨-69/640, -247/640⟩, 3/1280⟩
def center2646 : GaussianRat :=
  ⟨-87674459/1000000000, -278322741/1000000000⟩
def contact2646 : RatBall := localContactBall tau2646 center2646
def work2646 : RoundedTauEval :=
  evalTau precision tau2646 contact2646 logTwoBall

theorem center_sq2646 : (center2646.re : ℝ)^2 +
    (center2646.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2646]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2646 : work2646.theta.ok = true ∧
    work2646.jac.invOK = true ∧ acceptsUnitSq work2646.out = true := by decide +kernel

def cell2646 : CellCertificate where
  tauBall := tau2646
  contactCenter := center2646
  contactBall := contact2646
  work := work2646
  center_sq := center_sq2646
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2646.1
  jac_ok := checks2646.2.1
  accepted := checks2646.2.2

def tau2647 : RatBall :=
  ⟨⟨-71/640, -49/128⟩, 3/1280⟩
def center2647 : GaussianRat :=
  ⟨-44958767/500000000, -275574013/1000000000⟩
def contact2647 : RatBall := localContactBall tau2647 center2647
def work2647 : RoundedTauEval :=
  evalTau precision tau2647 contact2647 logTwoBall

theorem center_sq2647 : (center2647.re : ℝ)^2 +
    (center2647.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2647]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2647 : work2647.theta.ok = true ∧
    work2647.jac.invOK = true ∧ acceptsUnitSq work2647.out = true := by decide +kernel

def cell2647 : CellCertificate where
  tauBall := tau2647
  contactCenter := center2647
  contactBall := contact2647
  work := work2647
  center_sq := center_sq2647
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2647.1
  jac_ok := checks2647.2.1
  accepted := checks2647.2.2

def cells : List CellCertificate := [cell2640, cell2641, cell2642, cell2643, cell2644, cell2645, cell2646, cell2647]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330

end


