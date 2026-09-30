-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0365_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0365_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:02:39.48949+00:00
-- url     : https://prove2.me/theorems/30d3b7d1-2374-49c9-b02d-6b2b94faadad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0365 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2920 : RatBall :=
  ⟨⟨21/640, -51/128⟩, 3/1280⟩
def center2920 : GaussianRat :=
  ⟨27204153/1000000000, -58521471/200000000⟩
def contact2920 : RatBall := localContactBall tau2920 center2920
def work2920 : RoundedTauEval :=
  evalTau precision tau2920 contact2920 logTwoBall

theorem center_sq2920 : (center2920.re : ℝ)^2 +
    (center2920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2920 : work2920.theta.ok = true ∧
    work2920.jac.invOK = true ∧ acceptsUnitSq work2920.out = true := by decide +kernel

def cell2920 : CellCertificate where
  tauBall := tau2920
  contactCenter := center2920
  contactBall := contact2920
  work := work2920
  center_sq := center_sq2920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2920.1
  jac_ok := checks2920.2.1
  accepted := checks2920.2.2

def tau2921 : RatBall :=
  ⟨⟨23/640, -51/128⟩, 3/1280⟩
def center2921 : GaussianRat :=
  ⟨5958069/200000000, -292519767/1000000000⟩
def contact2921 : RatBall := localContactBall tau2921 center2921
def work2921 : RoundedTauEval :=
  evalTau precision tau2921 contact2921 logTwoBall

theorem center_sq2921 : (center2921.re : ℝ)^2 +
    (center2921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2921 : work2921.theta.ok = true ∧
    work2921.jac.invOK = true ∧ acceptsUnitSq work2921.out = true := by decide +kernel

def cell2921 : CellCertificate where
  tauBall := tau2921
  contactCenter := center2921
  contactBall := contact2921
  work := work2921
  center_sq := center_sq2921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2921.1
  jac_ok := checks2921.2.1
  accepted := checks2921.2.2

def tau2922 : RatBall :=
  ⟨⟨21/640, -253/640⟩, 3/1280⟩
def center2922 : GaussianRat :=
  ⟨5424219/200000000, -290024499/1000000000⟩
def contact2922 : RatBall := localContactBall tau2922 center2922
def work2922 : RoundedTauEval :=
  evalTau precision tau2922 contact2922 logTwoBall

theorem center_sq2922 : (center2922.re : ℝ)^2 +
    (center2922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2922 : work2922.theta.ok = true ∧
    work2922.jac.invOK = true ∧ acceptsUnitSq work2922.out = true := by decide +kernel

def cell2922 : CellCertificate where
  tauBall := tau2922
  contactCenter := center2922
  contactBall := contact2922
  work := work2922
  center_sq := center_sq2922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2922.1
  jac_ok := checks2922.2.1
  accepted := checks2922.2.2

def tau2923 : RatBall :=
  ⟨⟨23/640, -253/640⟩, 3/1280⟩
def center2923 : GaussianRat :=
  ⟨14849721/500000000, -7248453/25000000⟩
def contact2923 : RatBall := localContactBall tau2923 center2923
def work2923 : RoundedTauEval :=
  evalTau precision tau2923 contact2923 logTwoBall

theorem center_sq2923 : (center2923.re : ℝ)^2 +
    (center2923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2923 : work2923.theta.ok = true ∧
    work2923.jac.invOK = true ∧ acceptsUnitSq work2923.out = true := by decide +kernel

def cell2923 : CellCertificate where
  tauBall := tau2923
  contactCenter := center2923
  contactBall := contact2923
  work := work2923
  center_sq := center_sq2923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2923.1
  jac_ok := checks2923.2.1
  accepted := checks2923.2.2

def tau2924 : RatBall :=
  ⟨⟨17/640, -251/640⟩, 3/1280⟩
def center2924 : GaussianRat :=
  ⟨21894677/1000000000, -143798363/500000000⟩
def contact2924 : RatBall := localContactBall tau2924 center2924
def work2924 : RoundedTauEval :=
  evalTau precision tau2924 contact2924 logTwoBall

theorem center_sq2924 : (center2924.re : ℝ)^2 +
    (center2924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2924 : work2924.theta.ok = true ∧
    work2924.jac.invOK = true ∧ acceptsUnitSq work2924.out = true := by decide +kernel

def cell2924 : CellCertificate where
  tauBall := tau2924
  contactCenter := center2924
  contactBall := contact2924
  work := work2924
  center_sq := center_sq2924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2924.1
  jac_ok := checks2924.2.1
  accepted := checks2924.2.2

def tau2925 : RatBall :=
  ⟨⟨19/640, -251/640⟩, 3/1280⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365


