-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0364
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0364
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:56:39.838109+00:00
-- url     : https://prove2.me/theorems/459ea931-a4a5-41c8-af6a-d35b19806375
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0364.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2912 : RatBall :=
  ⟨⟨13/640, -251/640⟩, 3/1280⟩
def center2912 : GaussianRat :=
  ⟨8373251/500000000, -287713133/1000000000⟩
def contact2912 : RatBall := localContactBall tau2912 center2912
def work2912 : RoundedTauEval :=
  evalTau precision tau2912 contact2912 logTwoBall

theorem center_sq2912 : (center2912.re : ℝ)^2 +
    (center2912.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2912]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2912 : work2912.theta.ok = true ∧
    work2912.jac.invOK = true ∧ acceptsUnitSq work2912.out = true := by decide +kernel

def cell2912 : CellCertificate where
  tauBall := tau2912
  contactCenter := center2912
  contactBall := contact2912
  work := work2912
  center_sq := center_sq2912
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2912.1
  jac_ok := checks2912.2.1
  accepted := checks2912.2.2

def tau2913 : RatBall :=
  ⟨⟨3/128, -251/640⟩, 3/1280⟩
def center2913 : GaussianRat :=
  ⟨3864199/200000000, -57531759/200000000⟩
def contact2913 : RatBall := localContactBall tau2913 center2913
def work2913 : RoundedTauEval :=
  evalTau precision tau2913 contact2913 logTwoBall

theorem center_sq2913 : (center2913.re : ℝ)^2 +
    (center2913.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2913]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2913 : work2913.theta.ok = true ∧
    work2913.jac.invOK = true ∧ acceptsUnitSq work2913.out = true := by decide +kernel

def cell2913 : CellCertificate where
  tauBall := tau2913
  contactCenter := center2913
  contactBall := contact2913
  work := work2913
  center_sq := center_sq2913
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2913.1
  jac_ok := checks2913.2.1
  accepted := checks2913.2.2

def tau2914 : RatBall :=
  ⟨⟨13/640, -249/640⟩, 3/1280⟩
def center2914 : GaussianRat :=
  ⟨3339277/200000000, -71285531/250000000⟩
def contact2914 : RatBall := localContactBall tau2914 center2914
def work2914 : RoundedTauEval :=
  evalTau precision tau2914 contact2914 logTwoBall

theorem center_sq2914 : (center2914.re : ℝ)^2 +
    (center2914.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2914]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2914 : work2914.theta.ok = true ∧
    work2914.jac.invOK = true ∧ acceptsUnitSq work2914.out = true := by decide +kernel

def cell2914 : CellCertificate where
  tauBall := tau2914
  contactCenter := center2914
  contactBall := contact2914
  work := work2914
  center_sq := center_sq2914
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2914.1
  jac_ok := checks2914.2.1
  accepted := checks2914.2.2

def tau2915 : RatBall :=
  ⟨⟨3/128, -249/640⟩, 3/1280⟩
def center2915 : GaussianRat :=
  ⟨19263193/1000000000, -142544269/500000000⟩
def contact2915 : RatBall := localContactBall tau2915 center2915
def work2915 : RoundedTauEval :=
  evalTau precision tau2915 contact2915 logTwoBall

theorem center_sq2915 : (center2915.re : ℝ)^2 +
    (center2915.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2915]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2915 : work2915.theta.ok = true ∧
    work2915.jac.invOK = true ∧ acceptsUnitSq work2915.out = true := by decide +kernel

def cell2915 : CellCertificate where
  tauBall := tau2915
  contactCenter := center2915
  contactBall := contact2915
  work := work2915
  center_sq := center_sq2915
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2915.1
  jac_ok := checks2915.2.1
  accepted := checks2915.2.2

def tau2916 : RatBall :=
  ⟨⟨17/640, -51/128⟩, 3/1280⟩
def center2916 : GaussianRat :=
  ⟨22028391/1000000000, -146379397/500000000⟩
def contact2916 : RatBall := localContactBall tau2916 center2916
def work2916 : RoundedTauEval :=
  evalTau precision tau2916 contact2916 logTwoBall

theorem center_sq2916 : (center2916.re : ℝ)^2 +
    (center2916.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2916]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2916 : work2916.theta.ok = true ∧
    work2916.jac.invOK = true ∧ acceptsUnitSq work2916.out = true := by decide +kernel

def cell2916 : CellCertificate where
  tauBall := tau2916
  contactCenter := center2916
  contactBall := contact2916
  work := work2916
  center_sq := center_sq2916
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2916.1
  jac_ok := checks2916.2.1
  accepted := checks2916.2.2

def tau2917 : RatBall :=
  ⟨⟨19/640, -51/128⟩, 3/1280⟩
def center2917 : GaussianRat :=
  ⟨24616799/1000000000, -73171759/250000000⟩
def contact2917 : RatBall := localContactBall tau2917 center2917
def work2917 : RoundedTauEval :=
  evalTau precision tau2917 contact2917 logTwoBall

theorem center_sq2917 : (center2917.re : ℝ)^2 +
    (center2917.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2917]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2917 : work2917.theta.ok = true ∧
    work2917.jac.invOK = true ∧ acceptsUnitSq work2917.out = true := by decide +kernel

def cell2917 : CellCertificate where
  tauBall := tau2917
  contactCenter := center2917
  contactBall := contact2917
  work := work2917
  center_sq := center_sq2917
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2917.1
  jac_ok := checks2917.2.1
  accepted := checks2917.2.2

def tau2918 : RatBall :=
  ⟨⟨17/640, -253/640⟩, 3/1280⟩
def center2918 : GaussianRat :=
  ⟨21961069/1000000000, -145086923/500000000⟩
def contact2918 : RatBall := localContactBall tau2918 center2918
def work2918 : RoundedTauEval :=
  evalTau precision tau2918 contact2918 logTwoBall

theorem center_sq2918 : (center2918.re : ℝ)^2 +
    (center2918.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2918]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2918 : work2918.theta.ok = true ∧
    work2918.jac.invOK = true ∧ acceptsUnitSq work2918.out = true := by decide +kernel

def cell2918 : CellCertificate where
  tauBall := tau2918
  contactCenter := center2918
  contactBall := contact2918
  work := work2918
  center_sq := center_sq2918
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2918.1
  jac_ok := checks2918.2.1
  accepted := checks2918.2.2

def tau2919 : RatBall :=
  ⟨⟨19/640, -253/640⟩, 3/1280⟩
def center2919 : GaussianRat :=
  ⟨24541601/1000000000, -290103079/1000000000⟩
def contact2919 : RatBall := localContactBall tau2919 center2919
def work2919 : RoundedTauEval :=
  evalTau precision tau2919 contact2919 logTwoBall

theorem center_sq2919 : (center2919.re : ℝ)^2 +
    (center2919.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2919]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2919 : work2919.theta.ok = true ∧
    work2919.jac.invOK = true ∧ acceptsUnitSq work2919.out = true := by decide +kernel

def cell2919 : CellCertificate where
  tauBall := tau2919
  contactCenter := center2919
  contactBall := contact2919
  work := work2919
  center_sq := center_sq2919
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2919.1
  jac_ok := checks2919.2.1
  accepted := checks2919.2.2

def cells : List CellCertificate := [cell2912, cell2913, cell2914, cell2915, cell2916, cell2917, cell2918, cell2919]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364

end


