-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0260
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0260
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:35:42.251457+00:00
-- url     : https://prove2.me/theorems/566846de-980b-48b2-9d4e-1348277c0c20
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0260.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2080 : RatBall :=
  ⟨⟨-49/320, 111/320⟩, 3/640⟩
def center2080 : GaussianRat :=
  ⟨-29895113/250000000, 121954461/500000000⟩
def contact2080 : RatBall := localContactBall tau2080 center2080
def work2080 : RoundedTauEval :=
  evalTau precision tau2080 contact2080 logTwoBall

theorem center_sq2080 : (center2080.re : ℝ)^2 +
    (center2080.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2080]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2080 : work2080.theta.ok = true ∧
    work2080.jac.invOK = true ∧ acceptsUnitSq work2080.out = true := by decide +kernel

def cell2080 : CellCertificate where
  tauBall := tau2080
  contactCenter := center2080
  contactBall := contact2080
  work := work2080
  center_sq := center_sq2080
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2080.1
  jac_ok := checks2080.2.1
  accepted := checks2080.2.2

def tau2081 : RatBall :=
  ⟨⟨-47/320, 101/320⟩, 3/640⟩
def center2081 : GaussianRat :=
  ⟨-112208983/1000000000, 220920311/1000000000⟩
def contact2081 : RatBall := localContactBall tau2081 center2081
def work2081 : RoundedTauEval :=
  evalTau precision tau2081 contact2081 logTwoBall

theorem center_sq2081 : (center2081.re : ℝ)^2 +
    (center2081.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2081]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2081 : work2081.theta.ok = true ∧
    work2081.jac.invOK = true ∧ acceptsUnitSq work2081.out = true := by decide +kernel

def cell2081 : CellCertificate where
  tauBall := tau2081
  contactCenter := center2081
  contactBall := contact2081
  work := work2081
  center_sq := center_sq2081
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2081.1
  jac_ok := checks2081.2.1
  accepted := checks2081.2.2

def tau2082 : RatBall :=
  ⟨⟨-9/64, 101/320⟩, 3/640⟩
def center2082 : GaussianRat :=
  ⟨-53769161/500000000, 221399049/1000000000⟩
def contact2082 : RatBall := localContactBall tau2082 center2082
def work2082 : RoundedTauEval :=
  evalTau precision tau2082 contact2082 logTwoBall

theorem center_sq2082 : (center2082.re : ℝ)^2 +
    (center2082.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2082]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2082 : work2082.theta.ok = true ∧
    work2082.jac.invOK = true ∧ acceptsUnitSq work2082.out = true := by decide +kernel

def cell2082 : CellCertificate where
  tauBall := tau2082
  contactCenter := center2082
  contactBall := contact2082
  work := work2082
  center_sq := center_sq2082
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2082.1
  jac_ok := checks2082.2.1
  accepted := checks2082.2.2

def tau2083 : RatBall :=
  ⟨⟨-47/320, 103/320⟩, 3/640⟩
def center2083 : GaussianRat :=
  ⟨-704399/6250000, 112796733/500000000⟩
def contact2083 : RatBall := localContactBall tau2083 center2083
def work2083 : RoundedTauEval :=
  evalTau precision tau2083 contact2083 logTwoBall

theorem center_sq2083 : (center2083.re : ℝ)^2 +
    (center2083.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2083]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2083 : work2083.theta.ok = true ∧
    work2083.jac.invOK = true ∧ acceptsUnitSq work2083.out = true := by decide +kernel

def cell2083 : CellCertificate where
  tauBall := tau2083
  contactCenter := center2083
  contactBall := contact2083
  work := work2083
  center_sq := center_sq2083
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2083.1
  jac_ok := checks2083.2.1
  accepted := checks2083.2.2

def tau2084 : RatBall :=
  ⟨⟨-9/64, 103/320⟩, 3/640⟩
def center2084 : GaussianRat :=
  ⟨-21602887/200000000, 45217159/200000000⟩
def contact2084 : RatBall := localContactBall tau2084 center2084
def work2084 : RoundedTauEval :=
  evalTau precision tau2084 contact2084 logTwoBall

theorem center_sq2084 : (center2084.re : ℝ)^2 +
    (center2084.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2084]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2084 : work2084.theta.ok = true ∧
    work2084.jac.invOK = true ∧ acceptsUnitSq work2084.out = true := by decide +kernel

def cell2084 : CellCertificate where
  tauBall := tau2084
  contactCenter := center2084
  contactBall := contact2084
  work := work2084
  center_sq := center_sq2084
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2084.1
  jac_ok := checks2084.2.1
  accepted := checks2084.2.2

def tau2085 : RatBall :=
  ⟨⟨-47/320, 21/64⟩, 3/640⟩
def center2085 : GaussianRat :=
  ⟨-22642537/200000000, 230285467/1000000000⟩
def contact2085 : RatBall := localContactBall tau2085 center2085
def work2085 : RoundedTauEval :=
  evalTau precision tau2085 contact2085 logTwoBall

theorem center_sq2085 : (center2085.re : ℝ)^2 +
    (center2085.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2085]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2085 : work2085.theta.ok = true ∧
    work2085.jac.invOK = true ∧ acceptsUnitSq work2085.out = true := by decide +kernel

def cell2085 : CellCertificate where
  tauBall := tau2085
  contactCenter := center2085
  contactBall := contact2085
  work := work2085
  center_sq := center_sq2085
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2085.1
  jac_ok := checks2085.2.1
  accepted := checks2085.2.2

def tau2086 : RatBall :=
  ⟨⟨-9/64, 21/64⟩, 3/640⟩
def center2086 : GaussianRat :=
  ⟨-21700807/200000000, 115395841/500000000⟩
def contact2086 : RatBall := localContactBall tau2086 center2086
def work2086 : RoundedTauEval :=
  evalTau precision tau2086 contact2086 logTwoBall

theorem center_sq2086 : (center2086.re : ℝ)^2 +
    (center2086.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2086]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2086 : work2086.theta.ok = true ∧
    work2086.jac.invOK = true ∧ acceptsUnitSq work2086.out = true := by decide +kernel

def cell2086 : CellCertificate where
  tauBall := tau2086
  contactCenter := center2086
  contactBall := contact2086
  work := work2086
  center_sq := center_sq2086
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2086.1
  jac_ok := checks2086.2.1
  accepted := checks2086.2.2

def tau2087 : RatBall :=
  ⟨⟨-47/320, 107/320⟩, 3/640⟩
def center2087 : GaussianRat :=
  ⟨-56867911/500000000, 234996813/1000000000⟩
def contact2087 : RatBall := localContactBall tau2087 center2087
def work2087 : RoundedTauEval :=
  evalTau precision tau2087 contact2087 logTwoBall

theorem center_sq2087 : (center2087.re : ℝ)^2 +
    (center2087.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2087]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2087 : work2087.theta.ok = true ∧
    work2087.jac.invOK = true ∧ acceptsUnitSq work2087.out = true := by decide +kernel

def cell2087 : CellCertificate where
  tauBall := tau2087
  contactCenter := center2087
  contactBall := contact2087
  work := work2087
  center_sq := center_sq2087
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2087.1
  jac_ok := checks2087.2.1
  accepted := checks2087.2.2

def cells : List CellCertificate := [cell2080, cell2081, cell2082, cell2083, cell2084, cell2085, cell2086, cell2087]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260

end


