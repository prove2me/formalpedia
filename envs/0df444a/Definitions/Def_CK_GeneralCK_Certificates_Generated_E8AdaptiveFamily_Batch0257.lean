-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0257
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0257
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:04:39.602598+00:00
-- url     : https://prove2.me/theorems/db1bbd49-caeb-4858-9c64-a539d6c2f250
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0257.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2056 : RatBall :=
  ⟨⟨-57/320, 21/64⟩, 3/640⟩
def center2056 : GaussianRat :=
  ⟨-136531833/1000000000, 227470663/1000000000⟩
def contact2056 : RatBall := localContactBall tau2056 center2056
def work2056 : RoundedTauEval :=
  evalTau precision tau2056 contact2056 logTwoBall

theorem center_sq2056 : (center2056.re : ℝ)^2 +
    (center2056.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2056]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2056 : work2056.theta.ok = true ∧
    work2056.jac.invOK = true ∧ acceptsUnitSq work2056.out = true := by decide +kernel

def cell2056 : CellCertificate where
  tauBall := tau2056
  contactCenter := center2056
  contactBall := contact2056
  work := work2056
  center_sq := center_sq2056
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2056.1
  jac_ok := checks2056.2.1
  accepted := checks2056.2.2

def tau2057 : RatBall :=
  ⟨⟨-59/320, 107/320⟩, 3/640⟩
def center2057 : GaussianRat :=
  ⟨-141782257/1000000000, 231469249/1000000000⟩
def contact2057 : RatBall := localContactBall tau2057 center2057
def work2057 : RoundedTauEval :=
  evalTau precision tau2057 contact2057 logTwoBall

theorem center_sq2057 : (center2057.re : ℝ)^2 +
    (center2057.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2057]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2057 : work2057.theta.ok = true ∧
    work2057.jac.invOK = true ∧ acceptsUnitSq work2057.out = true := by decide +kernel

def cell2057 : CellCertificate where
  tauBall := tau2057
  contactCenter := center2057
  contactBall := contact2057
  work := work2057
  center_sq := center_sq2057
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2057.1
  jac_ok := checks2057.2.1
  accepted := checks2057.2.2

def tau2058 : RatBall :=
  ⟨⟨-57/320, 107/320⟩, 3/640⟩
def center2058 : GaussianRat :=
  ⟨-6857441/50000000, 46420737/200000000⟩
def contact2058 : RatBall := localContactBall tau2058 center2058
def work2058 : RoundedTauEval :=
  evalTau precision tau2058 contact2058 logTwoBall

theorem center_sq2058 : (center2058.re : ℝ)^2 +
    (center2058.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2058]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2058 : work2058.theta.ok = true ∧
    work2058.jac.invOK = true ∧ acceptsUnitSq work2058.out = true := by decide +kernel

def cell2058 : CellCertificate where
  tauBall := tau2058
  contactCenter := center2058
  contactBall := contact2058
  work := work2058
  center_sq := center_sq2058
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2058.1
  jac_ok := checks2058.2.1
  accepted := checks2058.2.2

def tau2059 : RatBall :=
  ⟨⟨-63/320, 109/320⟩, 3/640⟩
def center2059 : GaussianRat :=
  ⟨-75841877/500000000, 234745077/1000000000⟩
def contact2059 : RatBall := localContactBall tau2059 center2059
def work2059 : RoundedTauEval :=
  evalTau precision tau2059 contact2059 logTwoBall

theorem center_sq2059 : (center2059.re : ℝ)^2 +
    (center2059.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2059]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2059 : work2059.theta.ok = true ∧
    work2059.jac.invOK = true ∧ acceptsUnitSq work2059.out = true := by decide +kernel

def cell2059 : CellCertificate where
  tauBall := tau2059
  contactCenter := center2059
  contactBall := contact2059
  work := work2059
  center_sq := center_sq2059
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2059.1
  jac_ok := checks2059.2.1
  accepted := checks2059.2.2

def tau2060 : RatBall :=
  ⟨⟨-61/320, 109/320⟩, 3/640⟩
def center2060 : GaussianRat :=
  ⟨-147068213/1000000000, 14714559/62500000⟩
def contact2060 : RatBall := localContactBall tau2060 center2060
def work2060 : RoundedTauEval :=
  evalTau precision tau2060 contact2060 logTwoBall

theorem center_sq2060 : (center2060.re : ℝ)^2 +
    (center2060.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2060]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2060 : work2060.theta.ok = true ∧
    work2060.jac.invOK = true ∧ acceptsUnitSq work2060.out = true := by decide +kernel

def cell2060 : CellCertificate where
  tauBall := tau2060
  contactCenter := center2060
  contactBall := contact2060
  work := work2060
  center_sq := center_sq2060
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2060.1
  jac_ok := checks2060.2.1
  accepted := checks2060.2.2

def tau2061 : RatBall :=
  ⟨⟨-59/320, 109/320⟩, 3/640⟩
def center2061 : GaussianRat :=
  ⟨-71217211/500000000, 236102993/1000000000⟩
def contact2061 : RatBall := localContactBall tau2061 center2061
def work2061 : RoundedTauEval :=
  evalTau precision tau2061 contact2061 logTwoBall

theorem center_sq2061 : (center2061.re : ℝ)^2 +
    (center2061.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2061]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2061 : work2061.theta.ok = true ∧
    work2061.jac.invOK = true ∧ acceptsUnitSq work2061.out = true := by decide +kernel

def cell2061 : CellCertificate where
  tauBall := tau2061
  contactCenter := center2061
  contactBall := contact2061
  work := work2061
  center_sq := center_sq2061
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2061.1
  jac_ok := checks2061.2.1
  accepted := checks2061.2.2

def tau2062 : RatBall :=
  ⟨⟨-57/320, 109/320⟩, 3/640⟩
def center2062 : GaussianRat :=
  ⟨-137782813/1000000000, 5918871/25000000⟩
def contact2062 : RatBall := localContactBall tau2062 center2062
def work2062 : RoundedTauEval :=
  evalTau precision tau2062 contact2062 logTwoBall

theorem center_sq2062 : (center2062.re : ℝ)^2 +
    (center2062.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2062]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2062 : work2062.theta.ok = true ∧
    work2062.jac.invOK = true ∧ acceptsUnitSq work2062.out = true := by decide +kernel

def cell2062 : CellCertificate where
  tauBall := tau2062
  contactCenter := center2062
  contactBall := contact2062
  work := work2062
  center_sq := center_sq2062
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2062.1
  jac_ok := checks2062.2.1
  accepted := checks2062.2.2

def tau2063 : RatBall :=
  ⟨⟨-59/320, 111/320⟩, 3/640⟩
def center2063 : GaussianRat :=
  ⟨-143104409/1000000000, 240754941/1000000000⟩
def contact2063 : RatBall := localContactBall tau2063 center2063
def work2063 : RoundedTauEval :=
  evalTau precision tau2063 contact2063 logTwoBall

theorem center_sq2063 : (center2063.re : ℝ)^2 +
    (center2063.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2063]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2063 : work2063.theta.ok = true ∧
    work2063.jac.invOK = true ∧ acceptsUnitSq work2063.out = true := by decide +kernel

def cell2063 : CellCertificate where
  tauBall := tau2063
  contactCenter := center2063
  contactBall := contact2063
  work := work2063
  center_sq := center_sq2063
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2063.1
  jac_ok := checks2063.2.1
  accepted := checks2063.2.2

def cells : List CellCertificate := [cell2056, cell2057, cell2058, cell2059, cell2060, cell2061, cell2062, cell2063]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257

end


