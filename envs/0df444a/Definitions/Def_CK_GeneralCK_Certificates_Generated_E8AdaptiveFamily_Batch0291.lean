-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0291
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0291
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:32:20.489995+00:00
-- url     : https://prove2.me/theorems/20304e3e-241a-46c7-9eb1-45855cb9609e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0291.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2328 : RatBall :=
  ⟨⟨41/320, 21/64⟩, 3/640⟩
def center2328 : GaussianRat :=
  ⟨12380739/125000000, 115872433/500000000⟩
def contact2328 : RatBall := localContactBall tau2328 center2328
def work2328 : RoundedTauEval :=
  evalTau precision tau2328 contact2328 logTwoBall

theorem center_sq2328 : (center2328.re : ℝ)^2 +
    (center2328.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2328]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2328 : work2328.theta.ok = true ∧
    work2328.jac.invOK = true ∧ acceptsUnitSq work2328.out = true := by decide +kernel

def cell2328 : CellCertificate where
  tauBall := tau2328
  contactCenter := center2328
  contactBall := contact2328
  work := work2328
  center_sq := center_sq2328
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2328.1
  jac_ok := checks2328.2.1
  accepted := checks2328.2.2

def tau2329 : RatBall :=
  ⟨⟨43/320, 21/64⟩, 3/640⟩
def center2329 : GaussianRat :=
  ⟨103781603/1000000000, 28909781/125000000⟩
def contact2329 : RatBall := localContactBall tau2329 center2329
def work2329 : RoundedTauEval :=
  evalTau precision tau2329 contact2329 logTwoBall

theorem center_sq2329 : (center2329.re : ℝ)^2 +
    (center2329.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2329]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2329 : work2329.theta.ok = true ∧
    work2329.jac.invOK = true ∧ acceptsUnitSq work2329.out = true := by decide +kernel

def cell2329 : CellCertificate where
  tauBall := tau2329
  contactCenter := center2329
  contactBall := contact2329
  work := work2329
  center_sq := center_sq2329
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2329.1
  jac_ok := checks2329.2.1
  accepted := checks2329.2.2

def tau2330 : RatBall :=
  ⟨⟨41/320, 107/320⟩, 3/640⟩
def center2330 : GaussianRat :=
  ⟨99508871/1000000000, 236497219/1000000000⟩
def contact2330 : RatBall := localContactBall tau2330 center2330
def work2330 : RoundedTauEval :=
  evalTau precision tau2330 contact2330 logTwoBall

theorem center_sq2330 : (center2330.re : ℝ)^2 +
    (center2330.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2330]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2330 : work2330.theta.ok = true ∧
    work2330.jac.invOK = true ∧ acceptsUnitSq work2330.out = true := by decide +kernel

def cell2330 : CellCertificate where
  tauBall := tau2330
  contactCenter := center2330
  contactBall := contact2330
  work := work2330
  center_sq := center_sq2330
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2330.1
  jac_ok := checks2330.2.1
  accepted := checks2330.2.2

def tau2331 : RatBall :=
  ⟨⟨43/320, 107/320⟩, 3/640⟩
def center2331 : GaussianRat :=
  ⟨104264923/1000000000, 236017459/1000000000⟩
def contact2331 : RatBall := localContactBall tau2331 center2331
def work2331 : RoundedTauEval :=
  evalTau precision tau2331 contact2331 logTwoBall

theorem center_sq2331 : (center2331.re : ℝ)^2 +
    (center2331.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2331]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2331 : work2331.theta.ok = true ∧
    work2331.jac.invOK = true ∧ acceptsUnitSq work2331.out = true := by decide +kernel

def cell2331 : CellCertificate where
  tauBall := tau2331
  contactCenter := center2331
  contactBall := contact2331
  work := work2331
  center_sq := center_sq2331
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2331.1
  jac_ok := checks2331.2.1
  accepted := checks2331.2.2

def tau2332 : RatBall :=
  ⟨⟨9/64, 21/64⟩, 3/640⟩
def center2332 : GaussianRat :=
  ⟨21700807/200000000, 115395841/500000000⟩
def contact2332 : RatBall := localContactBall tau2332 center2332
def work2332 : RoundedTauEval :=
  evalTau precision tau2332 contact2332 logTwoBall

theorem center_sq2332 : (center2332.re : ℝ)^2 +
    (center2332.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2332]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2332 : work2332.theta.ok = true ∧
    work2332.jac.invOK = true ∧ acceptsUnitSq work2332.out = true := by decide +kernel

def cell2332 : CellCertificate where
  tauBall := tau2332
  contactCenter := center2332
  contactBall := contact2332
  work := work2332
  center_sq := center_sq2332
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2332.1
  jac_ok := checks2332.2.1
  accepted := checks2332.2.2

def tau2333 : RatBall :=
  ⟨⟨47/320, 21/64⟩, 3/640⟩
def center2333 : GaussianRat :=
  ⟨22642537/200000000, 230285467/1000000000⟩
def contact2333 : RatBall := localContactBall tau2333 center2333
def work2333 : RoundedTauEval :=
  evalTau precision tau2333 contact2333 logTwoBall

theorem center_sq2333 : (center2333.re : ℝ)^2 +
    (center2333.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2333]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2333 : work2333.theta.ok = true ∧
    work2333.jac.invOK = true ∧ acceptsUnitSq work2333.out = true := by decide +kernel

def cell2333 : CellCertificate where
  tauBall := tau2333
  contactCenter := center2333
  contactBall := contact2333
  work := work2333
  center_sq := center_sq2333
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2333.1
  jac_ok := checks2333.2.1
  accepted := checks2333.2.2

def tau2334 : RatBall :=
  ⟨⟨9/64, 107/320⟩, 3/640⟩
def center2334 : GaussianRat :=
  ⟨109007417/1000000000, 235517221/1000000000⟩
def contact2334 : RatBall := localContactBall tau2334 center2334
def work2334 : RoundedTauEval :=
  evalTau precision tau2334 contact2334 logTwoBall

theorem center_sq2334 : (center2334.re : ℝ)^2 +
    (center2334.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2334]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2334 : work2334.theta.ok = true ∧
    work2334.jac.invOK = true ∧ acceptsUnitSq work2334.out = true := by decide +kernel

def cell2334 : CellCertificate where
  tauBall := tau2334
  contactCenter := center2334
  contactBall := contact2334
  work := work2334
  center_sq := center_sq2334
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2334.1
  jac_ok := checks2334.2.1
  accepted := checks2334.2.2

def tau2335 : RatBall :=
  ⟨⟨47/320, 107/320⟩, 3/640⟩
def center2335 : GaussianRat :=
  ⟨56867911/500000000, 234996813/1000000000⟩
def contact2335 : RatBall := localContactBall tau2335 center2335
def work2335 : RoundedTauEval :=
  evalTau precision tau2335 contact2335 logTwoBall

theorem center_sq2335 : (center2335.re : ℝ)^2 +
    (center2335.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2335]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2335 : work2335.theta.ok = true ∧
    work2335.jac.invOK = true ∧ acceptsUnitSq work2335.out = true := by decide +kernel

def cell2335 : CellCertificate where
  tauBall := tau2335
  contactCenter := center2335
  contactBall := contact2335
  work := work2335
  center_sq := center_sq2335
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2335.1
  jac_ok := checks2335.2.1
  accepted := checks2335.2.2

def cells : List CellCertificate := [cell2328, cell2329, cell2330, cell2331, cell2332, cell2333, cell2334, cell2335]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291

end


