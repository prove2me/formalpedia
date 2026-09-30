-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0367
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0367
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:36:27.894413+00:00
-- url     : https://prove2.me/theorems/1cc70ef0-6436-40d9-9e35-a1c2680f7a60
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0367.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2936 : RatBall :=
  ⟨⟨29/640, -51/128⟩, 3/1280⟩
def center2936 : GaussianRat :=
  ⟨2346303/62500000, -292209741/1000000000⟩
def contact2936 : RatBall := localContactBall tau2936 center2936
def work2936 : RoundedTauEval :=
  evalTau precision tau2936 contact2936 logTwoBall

theorem center_sq2936 : (center2936.re : ℝ)^2 +
    (center2936.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2936]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2936 : work2936.theta.ok = true ∧
    work2936.jac.invOK = true ∧ acceptsUnitSq work2936.out = true := by decide +kernel

def cell2936 : CellCertificate where
  tauBall := tau2936
  contactCenter := center2936
  contactBall := contact2936
  work := work2936
  center_sq := center_sq2936
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2936.1
  jac_ok := checks2936.2.1
  accepted := checks2936.2.2

def tau2937 : RatBall :=
  ⟨⟨31/640, -51/128⟩, 3/1280⟩
def center2937 : GaussianRat :=
  ⟨20060649/500000000, -146045357/500000000⟩
def contact2937 : RatBall := localContactBall tau2937 center2937
def work2937 : RoundedTauEval :=
  evalTau precision tau2937 contact2937 logTwoBall

theorem center_sq2937 : (center2937.re : ℝ)^2 +
    (center2937.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2937]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2937 : work2937.theta.ok = true ∧
    work2937.jac.invOK = true ∧ acceptsUnitSq work2937.out = true := by decide +kernel

def cell2937 : CellCertificate where
  tauBall := tau2937
  contactCenter := center2937
  contactBall := contact2937
  work := work2937
  center_sq := center_sq2937
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2937.1
  jac_ok := checks2937.2.1
  accepted := checks2937.2.2

def tau2938 : RatBall :=
  ⟨⟨29/640, -253/640⟩, 3/1280⟩
def center2938 : GaussianRat :=
  ⟨18713263/500000000, -289632371/1000000000⟩
def contact2938 : RatBall := localContactBall tau2938 center2938
def work2938 : RoundedTauEval :=
  evalTau precision tau2938 contact2938 logTwoBall

theorem center_sq2938 : (center2938.re : ℝ)^2 +
    (center2938.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2938]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2938 : work2938.theta.ok = true ∧
    work2938.jac.invOK = true ∧ acceptsUnitSq work2938.out = true := by decide +kernel

def cell2938 : CellCertificate where
  tauBall := tau2938
  contactCenter := center2938
  contactBall := contact2938
  work := work2938
  center_sq := center_sq2938
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2938.1
  jac_ok := checks2938.2.1
  accepted := checks2938.2.2

def tau2939 : RatBall :=
  ⟨⟨31/640, -253/640⟩, 3/1280⟩
def center2939 : GaussianRat :=
  ⟨9999803/250000000, -36189373/125000000⟩
def contact2939 : RatBall := localContactBall tau2939 center2939
def work2939 : RoundedTauEval :=
  evalTau precision tau2939 contact2939 logTwoBall

theorem center_sq2939 : (center2939.re : ℝ)^2 +
    (center2939.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2939]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2939 : work2939.theta.ok = true ∧
    work2939.jac.invOK = true ∧ acceptsUnitSq work2939.out = true := by decide +kernel

def cell2939 : CellCertificate where
  tauBall := tau2939
  contactCenter := center2939
  contactBall := contact2939
  work := work2939
  center_sq := center_sq2939
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2939.1
  jac_ok := checks2939.2.1
  accepted := checks2939.2.2

def tau2940 : RatBall :=
  ⟨⟨5/128, -251/640⟩, 3/1280⟩
def center2940 : GaussianRat :=
  ⟨32179167/1000000000, -57454279/200000000⟩
def contact2940 : RatBall := localContactBall tau2940 center2940
def work2940 : RoundedTauEval :=
  evalTau precision tau2940 contact2940 logTwoBall

theorem center_sq2940 : (center2940.re : ℝ)^2 +
    (center2940.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2940]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2940 : work2940.theta.ok = true ∧
    work2940.jac.invOK = true ∧ acceptsUnitSq work2940.out = true := by decide +kernel

def cell2940 : CellCertificate where
  tauBall := tau2940
  contactCenter := center2940
  contactBall := contact2940
  work := work2940
  center_sq := center_sq2940
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2940.1
  jac_ok := checks2940.2.1
  accepted := checks2940.2.2

def tau2941 : RatBall :=
  ⟨⟨27/640, -251/640⟩, 3/1280⟩
def center2941 : GaussianRat :=
  ⟨17373599/500000000, -287170877/1000000000⟩
def contact2941 : RatBall := localContactBall tau2941 center2941
def work2941 : RoundedTauEval :=
  evalTau precision tau2941 contact2941 logTwoBall

theorem center_sq2941 : (center2941.re : ℝ)^2 +
    (center2941.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2941]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2941 : work2941.theta.ok = true ∧
    work2941.jac.invOK = true ∧ acceptsUnitSq work2941.out = true := by decide +kernel

def cell2941 : CellCertificate where
  tauBall := tau2941
  contactCenter := center2941
  contactBall := contact2941
  work := work2941
  center_sq := center_sq2941
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2941.1
  jac_ok := checks2941.2.1
  accepted := checks2941.2.2

def tau2942 : RatBall :=
  ⟨⟨5/128, -249/640⟩, 3/1280⟩
def center2942 : GaussianRat :=
  ⟨32083143/1000000000, -142353243/500000000⟩
def contact2942 : RatBall := localContactBall tau2942 center2942
def work2942 : RoundedTauEval :=
  evalTau precision tau2942 contact2942 logTwoBall

theorem center_sq2942 : (center2942.re : ℝ)^2 +
    (center2942.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2942]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2942 : work2942.theta.ok = true ∧
    work2942.jac.invOK = true ∧ acceptsUnitSq work2942.out = true := by decide +kernel

def cell2942 : CellCertificate where
  tauBall := tau2942
  contactCenter := center2942
  contactBall := contact2942
  work := work2942
  center_sq := center_sq2942
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2942.1
  jac_ok := checks2942.2.1
  accepted := checks2942.2.2

def tau2943 : RatBall :=
  ⟨⟨27/640, -249/640⟩, 3/1280⟩
def center2943 : GaussianRat :=
  ⟨34643579/1000000000, -56921471/200000000⟩
def contact2943 : RatBall := localContactBall tau2943 center2943
def work2943 : RoundedTauEval :=
  evalTau precision tau2943 contact2943 logTwoBall

theorem center_sq2943 : (center2943.re : ℝ)^2 +
    (center2943.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2943]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2943 : work2943.theta.ok = true ∧
    work2943.jac.invOK = true ∧ acceptsUnitSq work2943.out = true := by decide +kernel

def cell2943 : CellCertificate where
  tauBall := tau2943
  contactCenter := center2943
  contactBall := contact2943
  work := work2943
  center_sq := center_sq2943
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2943.1
  jac_ok := checks2943.2.1
  accepted := checks2943.2.2

def cells : List CellCertificate := [cell2936, cell2937, cell2938, cell2939, cell2940, cell2941, cell2942, cell2943]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367

end


