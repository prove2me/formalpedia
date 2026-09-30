-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0402
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0402
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:57:43.560344+00:00
-- url     : https://prove2.me/theorems/a0dc7d3c-b4ea-4a98-b00e-7468b58342a1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0402.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3216 : RatBall :=
  ⟨⟨-129/640, 219/640⟩, 3/1280⟩
def center3216 : GaussianRat :=
  ⟨-155311177/1000000000, 29420787/125000000⟩
def contact3216 : RatBall := localContactBall tau3216 center3216
def work3216 : RoundedTauEval :=
  evalTau precision tau3216 contact3216 logTwoBall

theorem center_sq3216 : (center3216.re : ℝ)^2 +
    (center3216.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3216]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3216 : work3216.theta.ok = true ∧
    work3216.jac.invOK = true ∧ acceptsUnitSq work3216.out = true := by decide +kernel

def cell3216 : CellCertificate where
  tauBall := tau3216
  contactCenter := center3216
  contactBall := contact3216
  work := work3216
  center_sq := center_sq3216
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3216.1
  jac_ok := checks3216.2.1
  accepted := checks3216.2.2

def tau3217 : RatBall :=
  ⟨⟨-131/640, 221/640⟩, 3/1280⟩
def center3217 : GaussianRat :=
  ⟨-157970893/1000000000, 237302543/1000000000⟩
def contact3217 : RatBall := localContactBall tau3217 center3217
def work3217 : RoundedTauEval :=
  evalTau precision tau3217 contact3217 logTwoBall

theorem center_sq3217 : (center3217.re : ℝ)^2 +
    (center3217.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3217]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3217 : work3217.theta.ok = true ∧
    work3217.jac.invOK = true ∧ acceptsUnitSq work3217.out = true := by decide +kernel

def cell3217 : CellCertificate where
  tauBall := tau3217
  contactCenter := center3217
  contactBall := contact3217
  work := work3217
  center_sq := center_sq3217
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3217.1
  jac_ok := checks3217.2.1
  accepted := checks3217.2.2

def tau3218 : RatBall :=
  ⟨⟨-129/640, 221/640⟩, 3/1280⟩
def center3218 : GaussianRat :=
  ⟨-155670749/1000000000, 118833343/500000000⟩
def contact3218 : RatBall := localContactBall tau3218 center3218
def work3218 : RoundedTauEval :=
  evalTau precision tau3218 contact3218 logTwoBall

theorem center_sq3218 : (center3218.re : ℝ)^2 +
    (center3218.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3218]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3218 : work3218.theta.ok = true ∧
    work3218.jac.invOK = true ∧ acceptsUnitSq work3218.out = true := by decide +kernel

def cell3218 : CellCertificate where
  tauBall := tau3218
  contactCenter := center3218
  contactBall := contact3218
  work := work3218
  center_sq := center_sq3218
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3218.1
  jac_ok := checks3218.2.1
  accepted := checks3218.2.2

def tau3219 : RatBall :=
  ⟨⟨-127/640, 221/640⟩, 3/1280⟩
def center3219 : GaussianRat :=
  ⟨-38341447/250000000, 29753309/125000000⟩
def contact3219 : RatBall := localContactBall tau3219 center3219
def work3219 : RoundedTauEval :=
  evalTau precision tau3219 contact3219 logTwoBall

theorem center_sq3219 : (center3219.re : ℝ)^2 +
    (center3219.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3219]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3219 : work3219.theta.ok = true ∧
    work3219.jac.invOK = true ∧ acceptsUnitSq work3219.out = true := by decide +kernel

def cell3219 : CellCertificate where
  tauBall := tau3219
  contactCenter := center3219
  contactBall := contact3219
  work := work3219
  center_sq := center_sq3219
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3219.1
  jac_ok := checks3219.2.1
  accepted := checks3219.2.2

def tau3220 : RatBall :=
  ⟨⟨-25/128, 221/640⟩, 3/1280⟩
def center3220 : GaussianRat :=
  ⟨-151056059/1000000000, 238381849/1000000000⟩
def contact3220 : RatBall := localContactBall tau3220 center3220
def work3220 : RoundedTauEval :=
  evalTau precision tau3220 contact3220 logTwoBall

theorem center_sq3220 : (center3220.re : ℝ)^2 +
    (center3220.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3220]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3220 : work3220.theta.ok = true ∧
    work3220.jac.invOK = true ∧ acceptsUnitSq work3220.out = true := by decide +kernel

def cell3220 : CellCertificate where
  tauBall := tau3220
  contactCenter := center3220
  contactBall := contact3220
  work := work3220
  center_sq := center_sq3220
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3220.1
  jac_ok := checks3220.2.1
  accepted := checks3220.2.2

def tau3221 : RatBall :=
  ⟨⟨-127/640, 223/640⟩, 3/1280⟩
def center3221 : GaussianRat :=
  ⟨-153725769/1000000000, 120168019/500000000⟩
def contact3221 : RatBall := localContactBall tau3221 center3221
def work3221 : RoundedTauEval :=
  evalTau precision tau3221 contact3221 logTwoBall

theorem center_sq3221 : (center3221.re : ℝ)^2 +
    (center3221.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3221]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3221 : work3221.theta.ok = true ∧
    work3221.jac.invOK = true ∧ acceptsUnitSq work3221.out = true := by decide +kernel

def cell3221 : CellCertificate where
  tauBall := tau3221
  contactCenter := center3221
  contactBall := contact3221
  work := work3221
  center_sq := center_sq3221
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3221.1
  jac_ok := checks3221.2.1
  accepted := checks3221.2.2

def tau3222 : RatBall :=
  ⟨⟨-25/128, 223/640⟩, 3/1280⟩
def center3222 : GaussianRat :=
  ⟨-151411581/1000000000, 120348091/500000000⟩
def contact3222 : RatBall := localContactBall tau3222 center3222
def work3222 : RoundedTauEval :=
  evalTau precision tau3222 contact3222 logTwoBall

theorem center_sq3222 : (center3222.re : ℝ)^2 +
    (center3222.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3222]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3222 : work3222.theta.ok = true ∧
    work3222.jac.invOK = true ∧ acceptsUnitSq work3222.out = true := by decide +kernel

def cell3222 : CellCertificate where
  tauBall := tau3222
  contactCenter := center3222
  contactBall := contact3222
  work := work3222
  center_sq := center_sq3222
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3222.1
  jac_ok := checks3222.2.1
  accepted := checks3222.2.2

def tau3223 : RatBall :=
  ⟨⟨-123/640, 221/640⟩, 3/1280⟩
def center3223 : GaussianRat :=
  ⟨-29748323/200000000, 119366383/500000000⟩
def contact3223 : RatBall := localContactBall tau3223 center3223
def work3223 : RoundedTauEval :=
  evalTau precision tau3223 contact3223 logTwoBall

theorem center_sq3223 : (center3223.re : ℝ)^2 +
    (center3223.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3223]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3223 : work3223.theta.ok = true ∧
    work3223.jac.invOK = true ∧ acceptsUnitSq work3223.out = true := by decide +kernel

def cell3223 : CellCertificate where
  tauBall := tau3223
  contactCenter := center3223
  contactBall := contact3223
  work := work3223
  center_sq := center_sq3223
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3223.1
  jac_ok := checks3223.2.1
  accepted := checks3223.2.2

def cells : List CellCertificate := [cell3216, cell3217, cell3218, cell3219, cell3220, cell3221, cell3222, cell3223]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402

end


