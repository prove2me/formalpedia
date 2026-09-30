-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0265
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0265
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:03:00.391385+00:00
-- url     : https://prove2.me/theorems/2c176f06-d086-42ac-8266-e8efe1f10781
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0265.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2120 : RatBall :=
  ⟨⟨-41/320, 113/320⟩, 3/640⟩
def center2120 : GaussianRat :=
  ⟨-100977067/1000000000, 250881183/1000000000⟩
def contact2120 : RatBall := localContactBall tau2120 center2120
def work2120 : RoundedTauEval :=
  evalTau precision tau2120 contact2120 logTwoBall

theorem center_sq2120 : (center2120.re : ℝ)^2 +
    (center2120.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2120]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2120 : work2120.theta.ok = true ∧
    work2120.jac.invOK = true ∧ acceptsUnitSq work2120.out = true := by decide +kernel

def cell2120 : CellCertificate where
  tauBall := tau2120
  contactCenter := center2120
  contactBall := contact2120
  work := work2120
  center_sq := center_sq2120
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2120.1
  jac_ok := checks2120.2.1
  accepted := checks2120.2.2

def tau2121 : RatBall :=
  ⟨⟨-43/320, 23/64⟩, 3/640⟩
def center2121 : GaussianRat :=
  ⟨-106336973/1000000000, 255184583/1000000000⟩
def contact2121 : RatBall := localContactBall tau2121 center2121
def work2121 : RoundedTauEval :=
  evalTau precision tau2121 contact2121 logTwoBall

theorem center_sq2121 : (center2121.re : ℝ)^2 +
    (center2121.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2121]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2121 : work2121.theta.ok = true ∧
    work2121.jac.invOK = true ∧ acceptsUnitSq work2121.out = true := by decide +kernel

def cell2121 : CellCertificate where
  tauBall := tau2121
  contactCenter := center2121
  contactBall := contact2121
  work := work2121
  center_sq := center_sq2121
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2121.1
  jac_ok := checks2121.2.1
  accepted := checks2121.2.2

def tau2122 : RatBall :=
  ⟨⟨-41/320, 23/64⟩, 3/640⟩
def center2122 : GaussianRat :=
  ⟨-12686743/125000000, 255720023/1000000000⟩
def contact2122 : RatBall := localContactBall tau2122 center2122
def work2122 : RoundedTauEval :=
  evalTau precision tau2122 contact2122 logTwoBall

theorem center_sq2122 : (center2122.re : ℝ)^2 +
    (center2122.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2122]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2122 : work2122.theta.ok = true ∧
    work2122.jac.invOK = true ∧ acceptsUnitSq work2122.out = true := by decide +kernel

def cell2122 : CellCertificate where
  tauBall := tau2122
  contactCenter := center2122
  contactBall := contact2122
  work := work2122
  center_sq := center_sq2122
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2122.1
  jac_ok := checks2122.2.1
  accepted := checks2122.2.2

def tau2123 : RatBall :=
  ⟨⟨-39/320, 113/320⟩, 3/640⟩
def center2123 : GaussianRat :=
  ⟨-48071341/500000000, 251379737/1000000000⟩
def contact2123 : RatBall := localContactBall tau2123 center2123
def work2123 : RoundedTauEval :=
  evalTau precision tau2123 contact2123 logTwoBall

theorem center_sq2123 : (center2123.re : ℝ)^2 +
    (center2123.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2123]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2123 : work2123.theta.ok = true ∧
    work2123.jac.invOK = true ∧ acceptsUnitSq work2123.out = true := by decide +kernel

def cell2123 : CellCertificate where
  tauBall := tau2123
  contactCenter := center2123
  contactBall := contact2123
  work := work2123
  center_sq := center_sq2123
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2123.1
  jac_ok := checks2123.2.1
  accepted := checks2123.2.2

def tau2124 : RatBall :=
  ⟨⟨-37/320, 113/320⟩, 3/640⟩
def center2124 : GaussianRat :=
  ⟨-45647467/500000000, 62963873/250000000⟩
def contact2124 : RatBall := localContactBall tau2124 center2124
def work2124 : RoundedTauEval :=
  evalTau precision tau2124 contact2124 logTwoBall

theorem center_sq2124 : (center2124.re : ℝ)^2 +
    (center2124.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2124]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2124 : work2124.theta.ok = true ∧
    work2124.jac.invOK = true ∧ acceptsUnitSq work2124.out = true := by decide +kernel

def cell2124 : CellCertificate where
  tauBall := tau2124
  contactCenter := center2124
  contactBall := contact2124
  work := work2124
  center_sq := center_sq2124
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2124.1
  jac_ok := checks2124.2.1
  accepted := checks2124.2.2

def tau2125 : RatBall :=
  ⟨⟨-39/320, 23/64⟩, 3/640⟩
def center2125 : GaussianRat :=
  ⟨-773093/8000000, 128116201/500000000⟩
def contact2125 : RatBall := localContactBall tau2125 center2125
def work2125 : RoundedTauEval :=
  evalTau precision tau2125 contact2125 logTwoBall

theorem center_sq2125 : (center2125.re : ℝ)^2 +
    (center2125.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2125]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2125 : work2125.theta.ok = true ∧
    work2125.jac.invOK = true ∧ acceptsUnitSq work2125.out = true := by decide +kernel

def cell2125 : CellCertificate where
  tauBall := tau2125
  contactCenter := center2125
  contactBall := contact2125
  work := work2125
  center_sq := center_sq2125
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2125.1
  jac_ok := checks2125.2.1
  accepted := checks2125.2.2

def tau2126 : RatBall :=
  ⟨⟨-37/320, 23/64⟩, 3/640⟩
def center2126 : GaussianRat :=
  ⟨-91765617/1000000000, 12836069/50000000⟩
def contact2126 : RatBall := localContactBall tau2126 center2126
def work2126 : RoundedTauEval :=
  evalTau precision tau2126 contact2126 logTwoBall

theorem center_sq2126 : (center2126.re : ℝ)^2 +
    (center2126.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2126]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2126 : work2126.theta.ok = true ∧
    work2126.jac.invOK = true ∧ acceptsUnitSq work2126.out = true := by decide +kernel

def cell2126 : CellCertificate where
  tauBall := tau2126
  contactCenter := center2126
  contactBall := contact2126
  work := work2126
  center_sq := center_sq2126
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2126.1
  jac_ok := checks2126.2.1
  accepted := checks2126.2.2

def tau2127 : RatBall :=
  ⟨⟨-7/64, 113/320⟩, 3/640⟩
def center2127 : GaussianRat :=
  ⟨-86434423/1000000000, 50461627/200000000⟩
def contact2127 : RatBall := localContactBall tau2127 center2127
def work2127 : RoundedTauEval :=
  evalTau precision tau2127 contact2127 logTwoBall

theorem center_sq2127 : (center2127.re : ℝ)^2 +
    (center2127.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2127 : work2127.theta.ok = true ∧
    work2127.jac.invOK = true ∧ acceptsUnitSq work2127.out = true := by decide +kernel

def cell2127 : CellCertificate where
  tauBall := tau2127
  contactCenter := center2127
  contactBall := contact2127
  work := work2127
  center_sq := center_sq2127
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2127.1
  jac_ok := checks2127.2.1
  accepted := checks2127.2.2

def cells : List CellCertificate := [cell2120, cell2121, cell2122, cell2123, cell2124, cell2125, cell2126, cell2127]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265

end


