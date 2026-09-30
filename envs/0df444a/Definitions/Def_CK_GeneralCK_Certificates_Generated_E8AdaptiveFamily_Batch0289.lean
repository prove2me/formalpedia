-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0289
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0289
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:56:14.806688+00:00
-- url     : https://prove2.me/theorems/3d12138d-e164-40a2-b1ce-222aad10c4ea
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0289.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2312 : RatBall :=
  ⟨⟨9/64, 101/320⟩, 3/640⟩
def center2312 : GaussianRat :=
  ⟨53769161/500000000, 221399049/1000000000⟩
def contact2312 : RatBall := localContactBall tau2312 center2312
def work2312 : RoundedTauEval :=
  evalTau precision tau2312 contact2312 logTwoBall

theorem center_sq2312 : (center2312.re : ℝ)^2 +
    (center2312.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2312]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2312 : work2312.theta.ok = true ∧
    work2312.jac.invOK = true ∧ acceptsUnitSq work2312.out = true := by decide +kernel

def cell2312 : CellCertificate where
  tauBall := tau2312
  contactCenter := center2312
  contactBall := contact2312
  work := work2312
  center_sq := center_sq2312
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2312.1
  jac_ok := checks2312.2.1
  accepted := checks2312.2.2

def tau2313 : RatBall :=
  ⟨⟨47/320, 101/320⟩, 3/640⟩
def center2313 : GaussianRat :=
  ⟨112208983/1000000000, 220920311/1000000000⟩
def contact2313 : RatBall := localContactBall tau2313 center2313
def work2313 : RoundedTauEval :=
  evalTau precision tau2313 contact2313 logTwoBall

theorem center_sq2313 : (center2313.re : ℝ)^2 +
    (center2313.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2313]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2313 : work2313.theta.ok = true ∧
    work2313.jac.invOK = true ∧ acceptsUnitSq work2313.out = true := by decide +kernel

def cell2313 : CellCertificate where
  tauBall := tau2313
  contactCenter := center2313
  contactBall := contact2313
  work := work2313
  center_sq := center_sq2313
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2313.1
  jac_ok := checks2313.2.1
  accepted := checks2313.2.2

def tau2314 : RatBall :=
  ⟨⟨9/64, 103/320⟩, 3/640⟩
def center2314 : GaussianRat :=
  ⟨21602887/200000000, 45217159/200000000⟩
def contact2314 : RatBall := localContactBall tau2314 center2314
def work2314 : RoundedTauEval :=
  evalTau precision tau2314 contact2314 logTwoBall

theorem center_sq2314 : (center2314.re : ℝ)^2 +
    (center2314.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2314]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2314 : work2314.theta.ok = true ∧
    work2314.jac.invOK = true ∧ acceptsUnitSq work2314.out = true := by decide +kernel

def cell2314 : CellCertificate where
  tauBall := tau2314
  contactCenter := center2314
  contactBall := contact2314
  work := work2314
  center_sq := center_sq2314
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2314.1
  jac_ok := checks2314.2.1
  accepted := checks2314.2.2

def tau2315 : RatBall :=
  ⟨⟨47/320, 103/320⟩, 3/640⟩
def center2315 : GaussianRat :=
  ⟨704399/6250000, 112796733/500000000⟩
def contact2315 : RatBall := localContactBall tau2315 center2315
def work2315 : RoundedTauEval :=
  evalTau precision tau2315 contact2315 logTwoBall

theorem center_sq2315 : (center2315.re : ℝ)^2 +
    (center2315.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2315]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2315 : work2315.theta.ok = true ∧
    work2315.jac.invOK = true ∧ acceptsUnitSq work2315.out = true := by decide +kernel

def cell2315 : CellCertificate where
  tauBall := tau2315
  contactCenter := center2315
  contactBall := contact2315
  work := work2315
  center_sq := center_sq2315
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2315.1
  jac_ok := checks2315.2.1
  accepted := checks2315.2.2

def tau2316 : RatBall :=
  ⟨⟨37/320, 21/64⟩, 3/640⟩
def center2316 : GaussianRat :=
  ⟨89536891/1000000000, 116308561/500000000⟩
def contact2316 : RatBall := localContactBall tau2316 center2316
def work2316 : RoundedTauEval :=
  evalTau precision tau2316 contact2316 logTwoBall

theorem center_sq2316 : (center2316.re : ℝ)^2 +
    (center2316.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2316]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2316 : work2316.theta.ok = true ∧
    work2316.jac.invOK = true ∧ acceptsUnitSq work2316.out = true := by decide +kernel

def cell2316 : CellCertificate where
  tauBall := tau2316
  contactCenter := center2316
  contactBall := contact2316
  work := work2316
  center_sq := center_sq2316
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2316.1
  jac_ok := checks2316.2.1
  accepted := checks2316.2.2

def tau2317 : RatBall :=
  ⟨⟨39/320, 21/64⟩, 3/640⟩
def center2317 : GaussianRat :=
  ⟨94297493/1000000000, 185753/800000⟩
def contact2317 : RatBall := localContactBall tau2317 center2317
def work2317 : RoundedTauEval :=
  evalTau precision tau2317 contact2317 logTwoBall

theorem center_sq2317 : (center2317.re : ℝ)^2 +
    (center2317.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2317]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2317 : work2317.theta.ok = true ∧
    work2317.jac.invOK = true ∧ acceptsUnitSq work2317.out = true := by decide +kernel

def cell2317 : CellCertificate where
  tauBall := tau2317
  contactCenter := center2317
  contactBall := contact2317
  work := work2317
  center_sq := center_sq2317
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2317.1
  jac_ok := checks2317.2.1
  accepted := checks2317.2.2

def tau2318 : RatBall :=
  ⟨⟨37/320, 107/320⟩, 3/640⟩
def center2318 : GaussianRat :=
  ⟨22489569/250000000, 47478823/200000000⟩
def contact2318 : RatBall := localContactBall tau2318 center2318
def work2318 : RoundedTauEval :=
  evalTau precision tau2318 contact2318 logTwoBall

theorem center_sq2318 : (center2318.re : ℝ)^2 +
    (center2318.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2318]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2318 : work2318.theta.ok = true ∧
    work2318.jac.invOK = true ∧ acceptsUnitSq work2318.out = true := by decide +kernel

def cell2318 : CellCertificate where
  tauBall := tau2318
  contactCenter := center2318
  contactBall := contact2318
  work := work2318
  center_sq := center_sq2318
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2318.1
  jac_ok := checks2318.2.1
  accepted := checks2318.2.2

def tau2319 : RatBall :=
  ⟨⟨39/320, 107/320⟩, 3/640⟩
def center2319 : GaussianRat :=
  ⟨23684951/250000000, 1184781/5000000⟩
def contact2319 : RatBall := localContactBall tau2319 center2319
def work2319 : RoundedTauEval :=
  evalTau precision tau2319 contact2319 logTwoBall

theorem center_sq2319 : (center2319.re : ℝ)^2 +
    (center2319.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2319]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2319 : work2319.theta.ok = true ∧
    work2319.jac.invOK = true ∧ acceptsUnitSq work2319.out = true := by decide +kernel

def cell2319 : CellCertificate where
  tauBall := tau2319
  contactCenter := center2319
  contactBall := contact2319
  work := work2319
  center_sq := center_sq2319
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2319.1
  jac_ok := checks2319.2.1
  accepted := checks2319.2.2

def cells : List CellCertificate := [cell2312, cell2313, cell2314, cell2315, cell2316, cell2317, cell2318, cell2319]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289

end


