-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0254
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0254
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:40:38.000318+00:00
-- url     : https://prove2.me/theorems/07236127-fdd5-4897-8766-ae0026e2707f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0254.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2032 : RatBall :=
  ⟨⟨-57/320, 97/320⟩, 3/640⟩
def center2032 : GaussianRat :=
  ⟨-67113521/500000000, 52277787/250000000⟩
def contact2032 : RatBall := localContactBall tau2032 center2032
def work2032 : RoundedTauEval :=
  evalTau precision tau2032 contact2032 logTwoBall

theorem center_sq2032 : (center2032.re : ℝ)^2 +
    (center2032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2032 : work2032.theta.ok = true ∧
    work2032.jac.invOK = true ∧ acceptsUnitSq work2032.out = true := by decide +kernel

def cell2032 : CellCertificate where
  tauBall := tau2032
  contactCenter := center2032
  contactBall := contact2032
  work := work2032
  center_sq := center_sq2032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2032.1
  jac_ok := checks2032.2.1
  accepted := checks2032.2.2

def tau2033 : RatBall :=
  ⟨⟨-59/320, 99/320⟩, 3/640⟩
def center2033 : GaussianRat :=
  ⟨-34836127/250000000, 53276923/250000000⟩
def contact2033 : RatBall := localContactBall tau2033 center2033
def work2033 : RoundedTauEval :=
  evalTau precision tau2033 contact2033 logTwoBall

theorem center_sq2033 : (center2033.re : ℝ)^2 +
    (center2033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2033 : work2033.theta.ok = true ∧
    work2033.jac.invOK = true ∧ acceptsUnitSq work2033.out = true := by decide +kernel

def cell2033 : CellCertificate where
  tauBall := tau2033
  contactCenter := center2033
  contactBall := contact2033
  work := work2033
  center_sq := center_sq2033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2033.1
  jac_ok := checks2033.2.1
  accepted := checks2033.2.2

def tau2034 : RatBall :=
  ⟨⟨-57/320, 99/320⟩, 3/640⟩
def center2034 : GaussianRat :=
  ⟨-5391177/40000000, 106838001/500000000⟩
def contact2034 : RatBall := localContactBall tau2034 center2034
def work2034 : RoundedTauEval :=
  evalTau precision tau2034 contact2034 logTwoBall

theorem center_sq2034 : (center2034.re : ℝ)^2 +
    (center2034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2034 : work2034.theta.ok = true ∧
    work2034.jac.invOK = true ∧ acceptsUnitSq work2034.out = true := by decide +kernel

def cell2034 : CellCertificate where
  tauBall := tau2034
  contactCenter := center2034
  contactBall := contact2034
  work := work2034
  center_sq := center_sq2034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2034.1
  jac_ok := checks2034.2.1
  accepted := checks2034.2.2

def tau2035 : RatBall :=
  ⟨⟨-63/320, 101/320⟩, 3/640⟩
def center2035 : GaussianRat :=
  ⟨-74521233/500000000, 108227539/500000000⟩
def contact2035 : RatBall := localContactBall tau2035 center2035
def work2035 : RoundedTauEval :=
  evalTau precision tau2035 contact2035 logTwoBall

theorem center_sq2035 : (center2035.re : ℝ)^2 +
    (center2035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2035 : work2035.theta.ok = true ∧
    work2035.jac.invOK = true ∧ acceptsUnitSq work2035.out = true := by decide +kernel

def cell2035 : CellCertificate where
  tauBall := tau2035
  contactCenter := center2035
  contactBall := contact2035
  work := work2035
  center_sq := center_sq2035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2035.1
  jac_ok := checks2035.2.1
  accepted := checks2035.2.2

def tau2036 : RatBall :=
  ⟨⟨-61/320, 101/320⟩, 3/640⟩
def center2036 : GaussianRat :=
  ⟨-7224707/50000000, 217072079/1000000000⟩
def contact2036 : RatBall := localContactBall tau2036 center2036
def work2036 : RoundedTauEval :=
  evalTau precision tau2036 contact2036 logTwoBall

theorem center_sq2036 : (center2036.re : ℝ)^2 +
    (center2036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2036 : work2036.theta.ok = true ∧
    work2036.jac.invOK = true ∧ acceptsUnitSq work2036.out = true := by decide +kernel

def cell2036 : CellCertificate where
  tauBall := tau2036
  contactCenter := center2036
  contactBall := contact2036
  work := work2036
  center_sq := center_sq2036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2036.1
  jac_ok := checks2036.2.1
  accepted := checks2036.2.2

def tau2037 : RatBall :=
  ⟨⟨-63/320, 103/320⟩, 3/640⟩
def center2037 : GaussianRat :=
  ⟨-74838049/500000000, 221002847/1000000000⟩
def contact2037 : RatBall := localContactBall tau2037 center2037
def work2037 : RoundedTauEval :=
  evalTau precision tau2037 contact2037 logTwoBall

theorem center_sq2037 : (center2037.re : ℝ)^2 +
    (center2037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2037 : work2037.theta.ok = true ∧
    work2037.jac.invOK = true ∧ acceptsUnitSq work2037.out = true := by decide +kernel

def cell2037 : CellCertificate where
  tauBall := tau2037
  contactCenter := center2037
  contactBall := contact2037
  work := work2037
  center_sq := center_sq2037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2037.1
  jac_ok := checks2037.2.1
  accepted := checks2037.2.2

def tau2038 : RatBall :=
  ⟨⟨-61/320, 103/320⟩, 3/640⟩
def center2038 : GaussianRat :=
  ⟨-5804463/40000000, 221637027/1000000000⟩
def contact2038 : RatBall := localContactBall tau2038 center2038
def work2038 : RoundedTauEval :=
  evalTau precision tau2038 contact2038 logTwoBall

theorem center_sq2038 : (center2038.re : ℝ)^2 +
    (center2038.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2038]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2038 : work2038.theta.ok = true ∧
    work2038.jac.invOK = true ∧ acceptsUnitSq work2038.out = true := by decide +kernel

def cell2038 : CellCertificate where
  tauBall := tau2038
  contactCenter := center2038
  contactBall := contact2038
  work := work2038
  center_sq := center_sq2038
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2038.1
  jac_ok := checks2038.2.1
  accepted := checks2038.2.2

def tau2039 : RatBall :=
  ⟨⟨-59/320, 101/320⟩, 3/640⟩
def center2039 : GaussianRat :=
  ⟨-27985801/200000000, 54418229/250000000⟩
def contact2039 : RatBall := localContactBall tau2039 center2039
def work2039 : RoundedTauEval :=
  evalTau precision tau2039 contact2039 logTwoBall

theorem center_sq2039 : (center2039.re : ℝ)^2 +
    (center2039.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2039]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2039 : work2039.theta.ok = true ∧
    work2039.jac.invOK = true ∧ acceptsUnitSq work2039.out = true := by decide +kernel

def cell2039 : CellCertificate where
  tauBall := tau2039
  contactCenter := center2039
  contactBall := contact2039
  work := work2039
  center_sq := center_sq2039
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2039.1
  jac_ok := checks2039.2.1
  accepted := checks2039.2.2

def cells : List CellCertificate := [cell2032, cell2033, cell2034, cell2035, cell2036, cell2037, cell2038, cell2039]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254

end


