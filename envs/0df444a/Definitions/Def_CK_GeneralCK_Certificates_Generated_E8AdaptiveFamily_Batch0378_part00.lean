-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0378_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0378_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:31:44.580332+00:00
-- url     : https://prove2.me/theorems/2d42544c-00c1-416a-8402-6f22023867c9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0378 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3024 : RatBall :=
  ⟨⟨51/640, -243/640⟩, 3/1280⟩
def center3024 : GaussianRat :=
  ⟨32332713/500000000, -275263239/1000000000⟩
def contact3024 : RatBall := localContactBall tau3024 center3024
def work3024 : RoundedTauEval :=
  evalTau precision tau3024 contact3024 logTwoBall

theorem center_sq3024 : (center3024.re : ℝ)^2 +
    (center3024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3024 : work3024.theta.ok = true ∧
    work3024.jac.invOK = true ∧ acceptsUnitSq work3024.out = true := by decide +kernel

def cell3024 : CellCertificate where
  tauBall := tau3024
  contactCenter := center3024
  contactBall := contact3024
  work := work3024
  center_sq := center_sq3024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3024.1
  jac_ok := checks3024.2.1
  accepted := checks3024.2.2

def tau3025 : RatBall :=
  ⟨⟨49/640, -241/640⟩, 3/1280⟩
def center3025 : GaussianRat :=
  ⟨12394897/200000000, -272930361/1000000000⟩
def contact3025 : RatBall := localContactBall tau3025 center3025
def work3025 : RoundedTauEval :=
  evalTau precision tau3025 contact3025 logTwoBall

theorem center_sq3025 : (center3025.re : ℝ)^2 +
    (center3025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3025 : work3025.theta.ok = true ∧
    work3025.jac.invOK = true ∧ acceptsUnitSq work3025.out = true := by decide +kernel

def cell3025 : CellCertificate where
  tauBall := tau3025
  contactCenter := center3025
  contactBall := contact3025
  work := work3025
  center_sq := center_sq3025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3025.1
  jac_ok := checks3025.2.1
  accepted := checks3025.2.2

def tau3026 : RatBall :=
  ⟨⟨51/640, -241/640⟩, 3/1280⟩
def center3026 : GaussianRat :=
  ⟨16120741/250000000, -34094071/125000000⟩
def contact3026 : RatBall := localContactBall tau3026 center3026
def work3026 : RoundedTauEval :=
  evalTau precision tau3026 contact3026 logTwoBall

theorem center_sq3026 : (center3026.re : ℝ)^2 +
    (center3026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3026 : work3026.theta.ok = true ∧
    work3026.jac.invOK = true ∧ acceptsUnitSq work3026.out = true := by decide +kernel

def cell3026 : CellCertificate where
  tauBall := tau3026
  contactCenter := center3026
  contactBall := contact3026
  work := work3026
  center_sq := center_sq3026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3026.1
  jac_ok := checks3026.2.1
  accepted := checks3026.2.2

def tau3027 : RatBall :=
  ⟨⟨53/640, -243/640⟩, 3/1280⟩
def center3027 : GaussianRat :=
  ⟨67178257/1000000000, -137538033/500000000⟩
def contact3027 : RatBall := localContactBall tau3027 center3027
def work3027 : RoundedTauEval :=
  evalTau precision tau3027 contact3027 logTwoBall

theorem center_sq3027 : (center3027.re : ℝ)^2 +
    (center3027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3027 : work3027.theta.ok = true ∧
    work3027.jac.invOK = true ∧ acceptsUnitSq work3027.out = true := by decide +kernel

def cell3027 : CellCertificate where
  tauBall := tau3027
  contactCenter := center3027
  contactBall := contact3027
  work := work3027
  center_sq := center_sq3027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3027.1
  jac_ok := checks3027.2.1
  accepted := checks3027.2.2

def tau3028 : RatBall :=
  ⟨⟨11/128, -243/640⟩, 3/1280⟩
def center3028 : GaussianRat :=
  ⟨13937693/200000000, -54976403/200000000⟩
def contact3028 : RatBall := localContactBall tau3028 center3028
def work3028 : RoundedTauEval :=
  evalTau precision tau3028 contact3028 logTwoBall

theorem center_sq3028 : (center3028.re : ℝ)^2 +
    (center3028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3028 : work3028.theta.ok = true ∧
    work3028.jac.invOK = true ∧ acceptsUnitSq work3028.out = true := by decide +kernel

def cell3028 : CellCertificate where
  tauBall := tau3028
  contactCenter := center3028
  contactBall := contact3028
  work := work3028
  center_sq := center_sq3028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3028.1
  jac_ok := checks3028.2.1
  accepted := checks3028.2.2

def tau3029 : RatBall :=
  ⟨⟨53/640, -241/640⟩, 3/1280⟩
def center3029 : GaussianRat :=
  ⟨13397789/200000000, -54513591/200000000⟩
def contact3029 : RatBall := localContactBall tau3029 center3029
def work3029 : RoundedTauEval :=
  evalTau precision tau3029 contact3029 logTwoBall

theorem center_sq3029 : (center3029.re : ℝ)^2 +
    (center3029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3029 : work3029.theta.ok = true ∧
    work3029.jac.invOK = true ∧ acceptsUnitSq work3029.out = true := by decide +kernel

def cell3029 : CellCertificate where
  tauBall := tau3029
  contactCenter := center3029
  contactBall := contact3029
  work := work3029
  center_sq := center_sq3029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3029.1
  jac_ok := checks3029.2.1
  accepted := checks3029.2.2

def tau3030 : RatBall :=
  ⟨⟨11/128, -241/640⟩, 3/1280⟩
def center3030 : GaussianRat :=
  ⟨34746169/500000000, -68094139/250000000⟩
def contact3030 : RatBall := localContactBall tau3030 center3030

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378


