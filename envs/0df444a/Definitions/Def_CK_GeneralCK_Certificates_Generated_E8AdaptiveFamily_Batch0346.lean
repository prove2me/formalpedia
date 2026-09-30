-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0346
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0346
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:15:40.280972+00:00
-- url     : https://prove2.me/theorems/bad6d4be-36d6-423d-a546-ed34a1998875
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0346.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2768 : RatBall :=
  ⟨⟨-47/640, -251/640⟩, 3/1280⟩
def center2768 : GaussianRat :=
  ⟨-1508267/25000000, -71437399/250000000⟩
def contact2768 : RatBall := localContactBall tau2768 center2768
def work2768 : RoundedTauEval :=
  evalTau precision tau2768 contact2768 logTwoBall

theorem center_sq2768 : (center2768.re : ℝ)^2 +
    (center2768.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2768]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2768 : work2768.theta.ok = true ∧
    work2768.jac.invOK = true ∧ acceptsUnitSq work2768.out = true := by decide +kernel

def cell2768 : CellCertificate where
  tauBall := tau2768
  contactCenter := center2768
  contactBall := contact2768
  work := work2768
  center_sq := center_sq2768
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2768.1
  jac_ok := checks2768.2.1
  accepted := checks2768.2.2

def tau2769 : RatBall :=
  ⟨⟨-9/128, -251/640⟩, 3/1280⟩
def center2769 : GaussianRat :=
  ⟨-57781797/1000000000, -285925371/1000000000⟩
def contact2769 : RatBall := localContactBall tau2769 center2769
def work2769 : RoundedTauEval :=
  evalTau precision tau2769 contact2769 logTwoBall

theorem center_sq2769 : (center2769.re : ℝ)^2 +
    (center2769.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2769]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2769 : work2769.theta.ok = true ∧
    work2769.jac.invOK = true ∧ acceptsUnitSq work2769.out = true := by decide +kernel

def cell2769 : CellCertificate where
  tauBall := tau2769
  contactCenter := center2769
  contactBall := contact2769
  work := work2769
  center_sq := center_sq2769
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2769.1
  jac_ok := checks2769.2.1
  accepted := checks2769.2.2

def tau2770 : RatBall :=
  ⟨⟨-47/640, -249/640⟩, 3/1280⟩
def center2770 : GaussianRat :=
  ⟨-60152449/1000000000, -283205599/1000000000⟩
def contact2770 : RatBall := localContactBall tau2770 center2770
def work2770 : RoundedTauEval :=
  evalTau precision tau2770 contact2770 logTwoBall

theorem center_sq2770 : (center2770.re : ℝ)^2 +
    (center2770.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2770]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2770 : work2770.theta.ok = true ∧
    work2770.jac.invOK = true ∧ acceptsUnitSq work2770.out = true := by decide +kernel

def cell2770 : CellCertificate where
  tauBall := tau2770
  contactCenter := center2770
  contactBall := contact2770
  work := work2770
  center_sq := center_sq2770
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2770.1
  jac_ok := checks2770.2.1
  accepted := checks2770.2.2

def tau2771 : RatBall :=
  ⟨⟨-9/128, -249/640⟩, 3/1280⟩
def center2771 : GaussianRat :=
  ⟨-28805449/500000000, -141689483/500000000⟩
def contact2771 : RatBall := localContactBall tau2771 center2771
def work2771 : RoundedTauEval :=
  evalTau precision tau2771 contact2771 logTwoBall

theorem center_sq2771 : (center2771.re : ℝ)^2 +
    (center2771.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2771]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2771 : work2771.theta.ok = true ∧
    work2771.jac.invOK = true ∧ acceptsUnitSq work2771.out = true := by decide +kernel

def cell2771 : CellCertificate where
  tauBall := tau2771
  contactCenter := center2771
  contactBall := contact2771
  work := work2771
  center_sq := center_sq2771
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2771.1
  jac_ok := checks2771.2.1
  accepted := checks2771.2.2

def tau2772 : RatBall :=
  ⟨⟨-43/640, -251/640⟩, 3/1280⟩
def center2772 : GaussianRat :=
  ⟨-2761527/50000000, -286093747/1000000000⟩
def contact2772 : RatBall := localContactBall tau2772 center2772
def work2772 : RoundedTauEval :=
  evalTau precision tau2772 contact2772 logTwoBall

theorem center_sq2772 : (center2772.re : ℝ)^2 +
    (center2772.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2772]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2772 : work2772.theta.ok = true ∧
    work2772.jac.invOK = true ∧ acceptsUnitSq work2772.out = true := by decide +kernel

def cell2772 : CellCertificate where
  tauBall := tau2772
  contactCenter := center2772
  contactBall := contact2772
  work := work2772
  center_sq := center_sq2772
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2772.1
  jac_ok := checks2772.2.1
  accepted := checks2772.2.2

def tau2773 : RatBall :=
  ⟨⟨-41/640, -251/640⟩, 3/1280⟩
def center2773 : GaussianRat :=
  ⟨-52677009/1000000000, -143127347/500000000⟩
def contact2773 : RatBall := localContactBall tau2773 center2773
def work2773 : RoundedTauEval :=
  evalTau precision tau2773 contact2773 logTwoBall

theorem center_sq2773 : (center2773.re : ℝ)^2 +
    (center2773.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2773 : work2773.theta.ok = true ∧
    work2773.jac.invOK = true ∧ acceptsUnitSq work2773.out = true := by decide +kernel

def cell2773 : CellCertificate where
  tauBall := tau2773
  contactCenter := center2773
  contactBall := contact2773
  work := work2773
  center_sq := center_sq2773
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2773.1
  jac_ok := checks2773.2.1
  accepted := checks2773.2.2

def tau2774 : RatBall :=
  ⟨⟨-43/640, -249/640⟩, 3/1280⟩
def center2774 : GaussianRat :=
  ⟨-13766751/250000000, -141772517/500000000⟩
def contact2774 : RatBall := localContactBall tau2774 center2774
def work2774 : RoundedTauEval :=
  evalTau precision tau2774 contact2774 logTwoBall

theorem center_sq2774 : (center2774.re : ℝ)^2 +
    (center2774.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2774]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2774 : work2774.theta.ok = true ∧
    work2774.jac.invOK = true ∧ acceptsUnitSq work2774.out = true := by decide +kernel

def cell2774 : CellCertificate where
  tauBall := tau2774
  contactCenter := center2774
  contactBall := contact2774
  work := work2774
  center_sq := center_sq2774
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2774.1
  jac_ok := checks2774.2.1
  accepted := checks2774.2.2

def tau2775 : RatBall :=
  ⟨⟨-41/640, -249/640⟩, 3/1280⟩
def center2775 : GaussianRat :=
  ⟨-13130217/250000000, -283703773/1000000000⟩
def contact2775 : RatBall := localContactBall tau2775 center2775
def work2775 : RoundedTauEval :=
  evalTau precision tau2775 contact2775 logTwoBall

theorem center_sq2775 : (center2775.re : ℝ)^2 +
    (center2775.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2775]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2775 : work2775.theta.ok = true ∧
    work2775.jac.invOK = true ∧ acceptsUnitSq work2775.out = true := by decide +kernel

def cell2775 : CellCertificate where
  tauBall := tau2775
  contactCenter := center2775
  contactBall := contact2775
  work := work2775
  center_sq := center_sq2775
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2775.1
  jac_ok := checks2775.2.1
  accepted := checks2775.2.2

def cells : List CellCertificate := [cell2768, cell2769, cell2770, cell2771, cell2772, cell2773, cell2774, cell2775]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346

end


