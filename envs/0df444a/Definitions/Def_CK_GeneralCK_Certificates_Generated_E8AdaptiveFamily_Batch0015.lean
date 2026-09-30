-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0015
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0015
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:18:12.709694+00:00
-- url     : https://prove2.me/theorems/d828b8fa-0658-4112-a823-21d0495cfff3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0015.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0120 : RatBall :=
  ⟨⟨-13/80, -9/80⟩, 3/160⟩
def center0120 : GaussianRat :=
  ⟨-56522129/500000000, -76186323/1000000000⟩
def contact0120 : RatBall := localContactBall tau0120 center0120
def work0120 : RoundedTauEval :=
  evalTau precision tau0120 contact0120 logTwoBall

theorem center_sq0120 : (center0120.re : ℝ)^2 +
    (center0120.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0120]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0120 : work0120.theta.ok = true ∧
    work0120.jac.invOK = true ∧ acceptsUnitSq work0120.out = true := by decide +kernel

def cell0120 : CellCertificate where
  tauBall := tau0120
  contactCenter := center0120
  contactBall := contact0120
  work := work0120
  center_sq := center_sq0120
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0120.1
  jac_ok := checks0120.2.1
  accepted := checks0120.2.2

def tau0121 : RatBall :=
  ⟨⟨-7/80, -3/16⟩, 3/160⟩
def center0121 : GaussianRat :=
  ⟨-6275219/100000000, -65240079/500000000⟩
def contact0121 : RatBall := localContactBall tau0121 center0121
def work0121 : RoundedTauEval :=
  evalTau precision tau0121 contact0121 logTwoBall

theorem center_sq0121 : (center0121.re : ℝ)^2 +
    (center0121.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0121]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0121 : work0121.theta.ok = true ∧
    work0121.jac.invOK = true ∧ acceptsUnitSq work0121.out = true := by decide +kernel

def cell0121 : CellCertificate where
  tauBall := tau0121
  contactCenter := center0121
  contactBall := contact0121
  work := work0121
  center_sq := center_sq0121
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0121.1
  jac_ok := checks0121.2.1
  accepted := checks0121.2.2

def tau0122 : RatBall :=
  ⟨⟨-1/16, -3/16⟩, 3/160⟩
def center0122 : GaussianRat :=
  ⟨-22445977/500000000, -131018253/1000000000⟩
def contact0122 : RatBall := localContactBall tau0122 center0122
def work0122 : RoundedTauEval :=
  evalTau precision tau0122 contact0122 logTwoBall

theorem center_sq0122 : (center0122.re : ℝ)^2 +
    (center0122.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0122]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0122 : work0122.theta.ok = true ∧
    work0122.jac.invOK = true ∧ acceptsUnitSq work0122.out = true := by decide +kernel

def cell0122 : CellCertificate where
  tauBall := tau0122
  contactCenter := center0122
  contactBall := contact0122
  work := work0122
  center_sq := center_sq0122
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0122.1
  jac_ok := checks0122.2.1
  accepted := checks0122.2.2

def tau0123 : RatBall :=
  ⟨⟨-7/80, -13/80⟩, 3/160⟩
def center0123 : GaussianRat :=
  ⟨-31086987/500000000, -112745169/1000000000⟩
def contact0123 : RatBall := localContactBall tau0123 center0123
def work0123 : RoundedTauEval :=
  evalTau precision tau0123 contact0123 logTwoBall

theorem center_sq0123 : (center0123.re : ℝ)^2 +
    (center0123.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0123]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0123 : work0123.theta.ok = true ∧
    work0123.jac.invOK = true ∧ acceptsUnitSq work0123.out = true := by decide +kernel

def cell0123 : CellCertificate where
  tauBall := tau0123
  contactCenter := center0123
  contactBall := contact0123
  work := work0123
  center_sq := center_sq0123
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0123.1
  jac_ok := checks0123.2.1
  accepted := checks0123.2.2

def tau0124 : RatBall :=
  ⟨⟨-1/16, -13/80⟩, 3/160⟩
def center0124 : GaussianRat :=
  ⟨-44475471/1000000000, -14150393/125000000⟩
def contact0124 : RatBall := localContactBall tau0124 center0124
def work0124 : RoundedTauEval :=
  evalTau precision tau0124 contact0124 logTwoBall

theorem center_sq0124 : (center0124.re : ℝ)^2 +
    (center0124.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0124]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0124 : work0124.theta.ok = true ∧
    work0124.jac.invOK = true ∧ acceptsUnitSq work0124.out = true := by decide +kernel

def cell0124 : CellCertificate where
  tauBall := tau0124
  contactCenter := center0124
  contactBall := contact0124
  work := work0124
  center_sq := center_sq0124
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0124.1
  jac_ok := checks0124.2.1
  accepted := checks0124.2.2

def tau0125 : RatBall :=
  ⟨⟨1/80, -23/80⟩, 3/160⟩
def center0125 : GaussianRat :=
  ⟨4738451/500000000, -102628961/500000000⟩
def contact0125 : RatBall := localContactBall tau0125 center0125
def work0125 : RoundedTauEval :=
  evalTau precision tau0125 contact0125 logTwoBall

theorem center_sq0125 : (center0125.re : ℝ)^2 +
    (center0125.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0125]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0125 : work0125.theta.ok = true ∧
    work0125.jac.invOK = true ∧ acceptsUnitSq work0125.out = true := by decide +kernel

def cell0125 : CellCertificate where
  tauBall := tau0125
  contactCenter := center0125
  contactBall := contact0125
  work := work0125
  center_sq := center_sq0125
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0125.1
  jac_ok := checks0125.2.1
  accepted := checks0125.2.2

def tau0126 : RatBall :=
  ⟨⟨3/80, -23/80⟩, 3/160⟩
def center0126 : GaussianRat :=
  ⟨14206169/500000000, -204949543/1000000000⟩
def contact0126 : RatBall := localContactBall tau0126 center0126
def work0126 : RoundedTauEval :=
  evalTau precision tau0126 contact0126 logTwoBall

theorem center_sq0126 : (center0126.re : ℝ)^2 +
    (center0126.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0126]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0126 : work0126.theta.ok = true ∧
    work0126.jac.invOK = true ∧ acceptsUnitSq work0126.out = true := by decide +kernel

def cell0126 : CellCertificate where
  tauBall := tau0126
  contactCenter := center0126
  contactBall := contact0126
  work := work0126
  center_sq := center_sq0126
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0126.1
  jac_ok := checks0126.2.1
  accepted := checks0126.2.2

def tau0127 : RatBall :=
  ⟨⟨1/80, -21/80⟩, 3/160⟩
def center0127 : GaussianRat :=
  ⟨4665703/500000000, -93227751/500000000⟩
def contact0127 : RatBall := localContactBall tau0127 center0127
def work0127 : RoundedTauEval :=
  evalTau precision tau0127 contact0127 logTwoBall

theorem center_sq0127 : (center0127.re : ℝ)^2 +
    (center0127.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0127 : work0127.theta.ok = true ∧
    work0127.jac.invOK = true ∧ acceptsUnitSq work0127.out = true := by decide +kernel

def cell0127 : CellCertificate where
  tauBall := tau0127
  contactCenter := center0127
  contactBall := contact0127
  work := work0127
  center_sq := center_sq0127
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0127.1
  jac_ok := checks0127.2.1
  accepted := checks0127.2.2

def cells : List CellCertificate := [cell0120, cell0121, cell0122, cell0123, cell0124, cell0125, cell0126, cell0127]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015

end


