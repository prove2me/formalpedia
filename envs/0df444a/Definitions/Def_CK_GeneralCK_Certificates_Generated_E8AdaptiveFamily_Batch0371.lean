-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0371
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0371
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:32:12.626724+00:00
-- url     : https://prove2.me/theorems/13d3495e-80e0-488a-8dea-d7d586993ac9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0371.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2968 : RatBall :=
  ⟨⟨37/640, -251/640⟩, 3/1280⟩
def center2968 : GaussianRat :=
  ⟨4756353/100000000, -4477409/15625000⟩
def contact2968 : RatBall := localContactBall tau2968 center2968
def work2968 : RoundedTauEval :=
  evalTau precision tau2968 contact2968 logTwoBall

theorem center_sq2968 : (center2968.re : ℝ)^2 +
    (center2968.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2968]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2968 : work2968.theta.ok = true ∧
    work2968.jac.invOK = true ∧ acceptsUnitSq work2968.out = true := by decide +kernel

def cell2968 : CellCertificate where
  tauBall := tau2968
  contactCenter := center2968
  contactBall := contact2968
  work := work2968
  center_sq := center_sq2968
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2968.1
  jac_ok := checks2968.2.1
  accepted := checks2968.2.2

def tau2969 : RatBall :=
  ⟨⟨39/640, -251/640⟩, 3/1280⟩
def center2969 : GaussianRat :=
  ⟨10024261/200000000, -14320409/50000000⟩
def contact2969 : RatBall := localContactBall tau2969 center2969
def work2969 : RoundedTauEval :=
  evalTau precision tau2969 contact2969 logTwoBall

theorem center_sq2969 : (center2969.re : ℝ)^2 +
    (center2969.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2969]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2969 : work2969.theta.ok = true ∧
    work2969.jac.invOK = true ∧ acceptsUnitSq work2969.out = true := by decide +kernel

def cell2969 : CellCertificate where
  tauBall := tau2969
  contactCenter := center2969
  contactBall := contact2969
  work := work2969
  center_sq := center_sq2969
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2969.1
  jac_ok := checks2969.2.1
  accepted := checks2969.2.2

def tau2970 : RatBall :=
  ⟨⟨37/640, -249/640⟩, 3/1280⟩
def center2970 : GaussianRat :=
  ⟨11855567/250000000, -283999143/1000000000⟩
def contact2970 : RatBall := localContactBall tau2970 center2970
def work2970 : RoundedTauEval :=
  evalTau precision tau2970 contact2970 logTwoBall

theorem center_sq2970 : (center2970.re : ℝ)^2 +
    (center2970.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2970]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2970 : work2970.theta.ok = true ∧
    work2970.jac.invOK = true ∧ acceptsUnitSq work2970.out = true := by decide +kernel

def cell2970 : CellCertificate where
  tauBall := tau2970
  contactCenter := center2970
  contactBall := contact2970
  work := work2970
  center_sq := center_sq2970
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2970.1
  jac_ok := checks2970.2.1
  accepted := checks2970.2.2

def tau2971 : RatBall :=
  ⟨⟨39/640, -249/640⟩, 3/1280⟩
def center2971 : GaussianRat :=
  ⟨4997259/100000000, -17740947/62500000⟩
def contact2971 : RatBall := localContactBall tau2971 center2971
def work2971 : RoundedTauEval :=
  evalTau precision tau2971 contact2971 logTwoBall

theorem center_sq2971 : (center2971.re : ℝ)^2 +
    (center2971.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2971]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2971 : work2971.theta.ok = true ∧
    work2971.jac.invOK = true ∧ acceptsUnitSq work2971.out = true := by decide +kernel

def cell2971 : CellCertificate where
  tauBall := tau2971
  contactCenter := center2971
  contactBall := contact2971
  work := work2971
  center_sq := center_sq2971
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2971.1
  jac_ok := checks2971.2.1
  accepted := checks2971.2.2

def tau2972 : RatBall :=
  ⟨⟨41/640, -253/640⟩, 3/1280⟩
def center2972 : GaussianRat :=
  ⟨52835321/1000000000, -11552523/40000000⟩
def contact2972 : RatBall := localContactBall tau2972 center2972
def work2972 : RoundedTauEval :=
  evalTau precision tau2972 contact2972 logTwoBall

theorem center_sq2972 : (center2972.re : ℝ)^2 +
    (center2972.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2972]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2972 : work2972.theta.ok = true ∧
    work2972.jac.invOK = true ∧ acceptsUnitSq work2972.out = true := by decide +kernel

def cell2972 : CellCertificate where
  tauBall := tau2972
  contactCenter := center2972
  contactBall := contact2972
  work := work2972
  center_sq := center_sq2972
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2972.1
  jac_ok := checks2972.2.1
  accepted := checks2972.2.2

def tau2973 : RatBall :=
  ⟨⟨43/640, -253/640⟩, 3/1280⟩
def center2973 : GaussianRat :=
  ⟨55396349/1000000000, -28864989/100000000⟩
def contact2973 : RatBall := localContactBall tau2973 center2973
def work2973 : RoundedTauEval :=
  evalTau precision tau2973 contact2973 logTwoBall

theorem center_sq2973 : (center2973.re : ℝ)^2 +
    (center2973.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2973]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2973 : work2973.theta.ok = true ∧
    work2973.jac.invOK = true ∧ acceptsUnitSq work2973.out = true := by decide +kernel

def cell2973 : CellCertificate where
  tauBall := tau2973
  contactCenter := center2973
  contactBall := contact2973
  work := work2973
  center_sq := center_sq2973
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2973.1
  jac_ok := checks2973.2.1
  accepted := checks2973.2.2

def tau2974 : RatBall :=
  ⟨⟨9/128, -253/640⟩, 3/1280⟩
def center2974 : GaussianRat :=
  ⟨5795507/100000000, -288479173/1000000000⟩
def contact2974 : RatBall := localContactBall tau2974 center2974
def work2974 : RoundedTauEval :=
  evalTau precision tau2974 contact2974 logTwoBall

theorem center_sq2974 : (center2974.re : ℝ)^2 +
    (center2974.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2974]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2974 : work2974.theta.ok = true ∧
    work2974.jac.invOK = true ∧ acceptsUnitSq work2974.out = true := by decide +kernel

def cell2974 : CellCertificate where
  tauBall := tau2974
  contactCenter := center2974
  contactBall := contact2974
  work := work2974
  center_sq := center_sq2974
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2974.1
  jac_ok := checks2974.2.1
  accepted := checks2974.2.2

def tau2975 : RatBall :=
  ⟨⟨41/640, -251/640⟩, 3/1280⟩
def center2975 : GaussianRat :=
  ⟨52677009/1000000000, -143127347/500000000⟩
def contact2975 : RatBall := localContactBall tau2975 center2975
def work2975 : RoundedTauEval :=
  evalTau precision tau2975 contact2975 logTwoBall

theorem center_sq2975 : (center2975.re : ℝ)^2 +
    (center2975.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2975]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2975 : work2975.theta.ok = true ∧
    work2975.jac.invOK = true ∧ acceptsUnitSq work2975.out = true := by decide +kernel

def cell2975 : CellCertificate where
  tauBall := tau2975
  contactCenter := center2975
  contactBall := contact2975
  work := work2975
  center_sq := center_sq2975
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2975.1
  jac_ok := checks2975.2.1
  accepted := checks2975.2.2

def cells : List CellCertificate := [cell2968, cell2969, cell2970, cell2971, cell2972, cell2973, cell2974, cell2975]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371

end


