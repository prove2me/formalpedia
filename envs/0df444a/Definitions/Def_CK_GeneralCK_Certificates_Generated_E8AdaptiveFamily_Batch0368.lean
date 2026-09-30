-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0368
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0368
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:42.416024+00:00
-- url     : https://prove2.me/theorems/572044f4-ab90-4b18-816f-fe3f6686b587
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0368.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2944 : RatBall :=
  ⟨⟨29/640, -251/640⟩, 3/1280⟩
def center2944 : GaussianRat :=
  ⟨1865689/50000000, -287062723/1000000000⟩
def contact2944 : RatBall := localContactBall tau2944 center2944
def work2944 : RoundedTauEval :=
  evalTau precision tau2944 contact2944 logTwoBall

theorem center_sq2944 : (center2944.re : ℝ)^2 +
    (center2944.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2944]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2944 : work2944.theta.ok = true ∧
    work2944.jac.invOK = true ∧ acceptsUnitSq work2944.out = true := by decide +kernel

def cell2944 : CellCertificate where
  tauBall := tau2944
  contactCenter := center2944
  contactBall := contact2944
  work := work2944
  center_sq := center_sq2944
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2944.1
  jac_ok := checks2944.2.1
  accepted := checks2944.2.2

def tau2945 : RatBall :=
  ⟨⟨31/640, -251/640⟩, 3/1280⟩
def center2945 : GaussianRat :=
  ⟨4984851/125000000, -286946953/1000000000⟩
def contact2945 : RatBall := localContactBall tau2945 center2945
def work2945 : RoundedTauEval :=
  evalTau precision tau2945 contact2945 logTwoBall

theorem center_sq2945 : (center2945.re : ℝ)^2 +
    (center2945.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2945]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2945 : work2945.theta.ok = true ∧
    work2945.jac.invOK = true ∧ acceptsUnitSq work2945.out = true := by decide +kernel

def cell2945 : CellCertificate where
  tauBall := tau2945
  contactCenter := center2945
  contactBall := contact2945
  work := work2945
  center_sq := center_sq2945
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2945.1
  jac_ok := checks2945.2.1
  accepted := checks2945.2.2

def tau2946 : RatBall :=
  ⟨⟨29/640, -249/640⟩, 3/1280⟩
def center2946 : GaussianRat :=
  ⟨37202587/1000000000, -284500691/1000000000⟩
def contact2946 : RatBall := localContactBall tau2946 center2946
def work2946 : RoundedTauEval :=
  evalTau precision tau2946 contact2946 logTwoBall

theorem center_sq2946 : (center2946.re : ℝ)^2 +
    (center2946.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2946]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2946 : work2946.theta.ok = true ∧
    work2946.jac.invOK = true ∧ acceptsUnitSq work2946.out = true := by decide +kernel

def cell2946 : CellCertificate where
  tauBall := tau2946
  contactCenter := center2946
  contactBall := contact2946
  work := work2946
  center_sq := center_sq2946
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2946.1
  jac_ok := checks2946.2.1
  accepted := checks2946.2.2

def tau2947 : RatBall :=
  ⟨⟨31/640, -249/640⟩, 3/1280⟩
def center2947 : GaussianRat :=
  ⟨19880031/500000000, -56877303/200000000⟩
def contact2947 : RatBall := localContactBall tau2947 center2947
def work2947 : RoundedTauEval :=
  evalTau precision tau2947 contact2947 logTwoBall

theorem center_sq2947 : (center2947.re : ℝ)^2 +
    (center2947.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2947]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2947 : work2947.theta.ok = true ∧
    work2947.jac.invOK = true ∧ acceptsUnitSq work2947.out = true := by decide +kernel

def cell2947 : CellCertificate where
  tauBall := tau2947
  contactCenter := center2947
  contactBall := contact2947
  work := work2947
  center_sq := center_sq2947
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2947.1
  jac_ok := checks2947.2.1
  accepted := checks2947.2.2

def tau2948 : RatBall :=
  ⟨⟨21/640, -247/640⟩, 3/1280⟩
def center2948 : GaussianRat :=
  ⟨26878737/1000000000, -282322297/1000000000⟩
def contact2948 : RatBall := localContactBall tau2948 center2948
def work2948 : RoundedTauEval :=
  evalTau precision tau2948 contact2948 logTwoBall

theorem center_sq2948 : (center2948.re : ℝ)^2 +
    (center2948.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2948]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2948 : work2948.theta.ok = true ∧
    work2948.jac.invOK = true ∧ acceptsUnitSq work2948.out = true := by decide +kernel

def cell2948 : CellCertificate where
  tauBall := tau2948
  contactCenter := center2948
  contactBall := contact2948
  work := work2948
  center_sq := center_sq2948
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2948.1
  jac_ok := checks2948.2.1
  accepted := checks2948.2.2

def tau2949 : RatBall :=
  ⟨⟨23/640, -247/640⟩, 3/1280⟩
def center2949 : GaussianRat :=
  ⟨1839637/62500000, -141119723/500000000⟩
def contact2949 : RatBall := localContactBall tau2949 center2949
def work2949 : RoundedTauEval :=
  evalTau precision tau2949 contact2949 logTwoBall

theorem center_sq2949 : (center2949.re : ℝ)^2 +
    (center2949.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2949]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2949 : work2949.theta.ok = true ∧
    work2949.jac.invOK = true ∧ acceptsUnitSq work2949.out = true := by decide +kernel

def cell2949 : CellCertificate where
  tauBall := tau2949
  contactCenter := center2949
  contactBall := contact2949
  work := work2949
  center_sq := center_sq2949
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2949.1
  jac_ok := checks2949.2.1
  accepted := checks2949.2.2

def tau2950 : RatBall :=
  ⟨⟨21/640, -49/128⟩, 3/1280⟩
def center2950 : GaussianRat :=
  ⟨6700043/250000000, -139884999/500000000⟩
def contact2950 : RatBall := localContactBall tau2950 center2950
def work2950 : RoundedTauEval :=
  evalTau precision tau2950 contact2950 logTwoBall

theorem center_sq2950 : (center2950.re : ℝ)^2 +
    (center2950.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2950]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2950 : work2950.theta.ok = true ∧
    work2950.jac.invOK = true ∧ acceptsUnitSq work2950.out = true := by decide +kernel

def cell2950 : CellCertificate where
  tauBall := tau2950
  contactCenter := center2950
  contactBall := contact2950
  work := work2950
  center_sq := center_sq2950
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2950.1
  jac_ok := checks2950.2.1
  accepted := checks2950.2.2

def tau2951 : RatBall :=
  ⟨⟨23/640, -49/128⟩, 3/1280⟩
def center2951 : GaussianRat :=
  ⟨7337051/250000000, -279688291/1000000000⟩
def contact2951 : RatBall := localContactBall tau2951 center2951
def work2951 : RoundedTauEval :=
  evalTau precision tau2951 contact2951 logTwoBall

theorem center_sq2951 : (center2951.re : ℝ)^2 +
    (center2951.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2951]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2951 : work2951.theta.ok = true ∧
    work2951.jac.invOK = true ∧ acceptsUnitSq work2951.out = true := by decide +kernel

def cell2951 : CellCertificate where
  tauBall := tau2951
  contactCenter := center2951
  contactBall := contact2951
  work := work2951
  center_sq := center_sq2951
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2951.1
  jac_ok := checks2951.2.1
  accepted := checks2951.2.2

def cells : List CellCertificate := [cell2944, cell2945, cell2946, cell2947, cell2948, cell2949, cell2950, cell2951]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368

end


