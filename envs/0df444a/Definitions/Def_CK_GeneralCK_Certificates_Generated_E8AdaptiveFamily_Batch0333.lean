-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0333
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0333
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:01:41.878477+00:00
-- url     : https://prove2.me/theorems/038cf267-7769-4894-b490-a018328b2051
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0333.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2664 : RatBall :=
  ⟨⟨-93/640, -237/640⟩, 3/1280⟩
def center2664 : GaussianRat :=
  ⟨-115826349/1000000000, -52528557/200000000⟩
def contact2664 : RatBall := localContactBall tau2664 center2664
def work2664 : RoundedTauEval :=
  evalTau precision tau2664 contact2664 logTwoBall

theorem center_sq2664 : (center2664.re : ℝ)^2 +
    (center2664.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2664]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2664 : work2664.theta.ok = true ∧
    work2664.jac.invOK = true ∧ acceptsUnitSq work2664.out = true := by decide +kernel

def cell2664 : CellCertificate where
  tauBall := tau2664
  contactCenter := center2664
  contactBall := contact2664
  work := work2664
  center_sq := center_sq2664
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2664.1
  jac_ok := checks2664.2.1
  accepted := checks2664.2.2

def tau2665 : RatBall :=
  ⟨⟨-91/640, -239/640⟩, 3/1280⟩
def center2665 : GaussianRat :=
  ⟨-113703619/1000000000, -265378247/1000000000⟩
def contact2665 : RatBall := localContactBall tau2665 center2665
def work2665 : RoundedTauEval :=
  evalTau precision tau2665 contact2665 logTwoBall

theorem center_sq2665 : (center2665.re : ℝ)^2 +
    (center2665.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2665]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2665 : work2665.theta.ok = true ∧
    work2665.jac.invOK = true ∧ acceptsUnitSq work2665.out = true := by decide +kernel

def cell2665 : CellCertificate where
  tauBall := tau2665
  contactCenter := center2665
  contactBall := contact2665
  work := work2665
  center_sq := center_sq2665
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2665.1
  jac_ok := checks2665.2.1
  accepted := checks2665.2.2

def tau2666 : RatBall :=
  ⟨⟨-89/640, -239/640⟩, 3/1280⟩
def center2666 : GaussianRat :=
  ⟨-111267493/1000000000, -265680799/1000000000⟩
def contact2666 : RatBall := localContactBall tau2666 center2666
def work2666 : RoundedTauEval :=
  evalTau precision tau2666 contact2666 logTwoBall

theorem center_sq2666 : (center2666.re : ℝ)^2 +
    (center2666.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2666]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2666 : work2666.theta.ok = true ∧
    work2666.jac.invOK = true ∧ acceptsUnitSq work2666.out = true := by decide +kernel

def cell2666 : CellCertificate where
  tauBall := tau2666
  contactCenter := center2666
  contactBall := contact2666
  work := work2666
  center_sq := center_sq2666
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2666.1
  jac_ok := checks2666.2.1
  accepted := checks2666.2.2

def tau2667 : RatBall :=
  ⟨⟨-91/640, -237/640⟩, 3/1280⟩
def center2667 : GaussianRat :=
  ⟨-22680033/200000000, -131473549/500000000⟩
def contact2667 : RatBall := localContactBall tau2667 center2667
def work2667 : RoundedTauEval :=
  evalTau precision tau2667 contact2667 logTwoBall

theorem center_sq2667 : (center2667.re : ℝ)^2 +
    (center2667.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2667]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2667 : work2667.theta.ok = true ∧
    work2667.jac.invOK = true ∧ acceptsUnitSq work2667.out = true := by decide +kernel

def cell2667 : CellCertificate where
  tauBall := tau2667
  contactCenter := center2667
  contactBall := contact2667
  work := work2667
  center_sq := center_sq2667
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2667.1
  jac_ok := checks2667.2.1
  accepted := checks2667.2.2

def tau2668 : RatBall :=
  ⟨⟨-89/640, -237/640⟩, 3/1280⟩
def center2668 : GaussianRat :=
  ⟨-55484957/500000000, -65811399/250000000⟩
def contact2668 : RatBall := localContactBall tau2668 center2668
def work2668 : RoundedTauEval :=
  evalTau precision tau2668 contact2668 logTwoBall

theorem center_sq2668 : (center2668.re : ℝ)^2 +
    (center2668.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2668]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2668 : work2668.theta.ok = true ∧
    work2668.jac.invOK = true ∧ acceptsUnitSq work2668.out = true := by decide +kernel

def cell2668 : CellCertificate where
  tauBall := tau2668
  contactCenter := center2668
  contactBall := contact2668
  work := work2668
  center_sq := center_sq2668
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2668.1
  jac_ok := checks2668.2.1
  accepted := checks2668.2.2

def tau2669 : RatBall :=
  ⟨⟨-19/128, -47/128⟩, 3/1280⟩
def center2669 : GaussianRat :=
  ⟨-117937551/1000000000, -649789/2500000⟩
def contact2669 : RatBall := localContactBall tau2669 center2669
def work2669 : RoundedTauEval :=
  evalTau precision tau2669 contact2669 logTwoBall

theorem center_sq2669 : (center2669.re : ℝ)^2 +
    (center2669.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2669]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2669 : work2669.theta.ok = true ∧
    work2669.jac.invOK = true ∧ acceptsUnitSq work2669.out = true := by decide +kernel

def cell2669 : CellCertificate where
  tauBall := tau2669
  contactCenter := center2669
  contactBall := contact2669
  work := work2669
  center_sq := center_sq2669
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2669.1
  jac_ok := checks2669.2.1
  accepted := checks2669.2.2

def tau2670 : RatBall :=
  ⟨⟨-93/640, -47/128⟩, 3/1280⟩
def center2670 : GaussianRat :=
  ⟨-115521207/1000000000, -32527691/125000000⟩
def contact2670 : RatBall := localContactBall tau2670 center2670
def work2670 : RoundedTauEval :=
  evalTau precision tau2670 contact2670 logTwoBall

theorem center_sq2670 : (center2670.re : ℝ)^2 +
    (center2670.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2670]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2670 : work2670.theta.ok = true ∧
    work2670.jac.invOK = true ∧ acceptsUnitSq work2670.out = true := by decide +kernel

def cell2670 : CellCertificate where
  tauBall := tau2670
  contactCenter := center2670
  contactBall := contact2670
  work := work2670
  center_sq := center_sq2670
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2670.1
  jac_ok := checks2670.2.1
  accepted := checks2670.2.2

def tau2671 : RatBall :=
  ⟨⟨-19/128, -233/640⟩, 3/1280⟩
def center2671 : GaussianRat :=
  ⟨-7351929/62500000, -128752067/500000000⟩
def contact2671 : RatBall := localContactBall tau2671 center2671
def work2671 : RoundedTauEval :=
  evalTau precision tau2671 contact2671 logTwoBall

theorem center_sq2671 : (center2671.re : ℝ)^2 +
    (center2671.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2671]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2671 : work2671.theta.ok = true ∧
    work2671.jac.invOK = true ∧ acceptsUnitSq work2671.out = true := by decide +kernel

def cell2671 : CellCertificate where
  tauBall := tau2671
  contactCenter := center2671
  contactBall := contact2671
  work := work2671
  center_sq := center_sq2671
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2671.1
  jac_ok := checks2671.2.1
  accepted := checks2671.2.2

def cells : List CellCertificate := [cell2664, cell2665, cell2666, cell2667, cell2668, cell2669, cell2670, cell2671]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333

end


