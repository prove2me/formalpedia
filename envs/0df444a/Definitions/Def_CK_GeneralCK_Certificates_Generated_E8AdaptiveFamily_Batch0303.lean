-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0303
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0303
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:57:07.603196+00:00
-- url     : https://prove2.me/theorems/65b05b73-b34a-481e-b7e2-e21884073092
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0303.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2424 : RatBall :=
  ⟨⟨13/64, 93/320⟩, 3/640⟩
def center2424 : GaussianRat :=
  ⟨151148249/1000000000, 98926301/500000000⟩
def contact2424 : RatBall := localContactBall tau2424 center2424
def work2424 : RoundedTauEval :=
  evalTau precision tau2424 contact2424 logTwoBall

theorem center_sq2424 : (center2424.re : ℝ)^2 +
    (center2424.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2424]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2424 : work2424.theta.ok = true ∧
    work2424.jac.invOK = true ∧ acceptsUnitSq work2424.out = true := by decide +kernel

def cell2424 : CellCertificate where
  tauBall := tau2424
  contactCenter := center2424
  contactBall := contact2424
  work := work2424
  center_sq := center_sq2424
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2424.1
  jac_ok := checks2424.2.1
  accepted := checks2424.2.2

def tau2425 : RatBall :=
  ⟨⟨67/320, 93/320⟩, 3/640⟩
def center2425 : GaussianRat :=
  ⟨3112069/20000000, 197272757/1000000000⟩
def contact2425 : RatBall := localContactBall tau2425 center2425
def work2425 : RoundedTauEval :=
  evalTau precision tau2425 contact2425 logTwoBall

theorem center_sq2425 : (center2425.re : ℝ)^2 +
    (center2425.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2425]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2425 : work2425.theta.ok = true ∧
    work2425.jac.invOK = true ∧ acceptsUnitSq work2425.out = true := by decide +kernel

def cell2425 : CellCertificate where
  tauBall := tau2425
  contactCenter := center2425
  contactBall := contact2425
  work := work2425
  center_sq := center_sq2425
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2425.1
  jac_ok := checks2425.2.1
  accepted := checks2425.2.2

def tau2426 : RatBall :=
  ⟨⟨13/64, 19/64⟩, 3/640⟩
def center2426 : GaussianRat :=
  ⟨30345869/200000000, 40464617/200000000⟩
def contact2426 : RatBall := localContactBall tau2426 center2426
def work2426 : RoundedTauEval :=
  evalTau precision tau2426 contact2426 logTwoBall

theorem center_sq2426 : (center2426.re : ℝ)^2 +
    (center2426.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2426]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2426 : work2426.theta.ok = true ∧
    work2426.jac.invOK = true ∧ acceptsUnitSq work2426.out = true := by decide +kernel

def cell2426 : CellCertificate where
  tauBall := tau2426
  contactCenter := center2426
  contactBall := contact2426
  work := work2426
  center_sq := center_sq2426
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2426.1
  jac_ok := checks2426.2.1
  accepted := checks2426.2.2

def tau2427 : RatBall :=
  ⟨⟨67/320, 19/64⟩, 3/640⟩
def center2427 : GaussianRat :=
  ⟨78099293/500000000, 100863299/500000000⟩
def contact2427 : RatBall := localContactBall tau2427 center2427
def work2427 : RoundedTauEval :=
  evalTau precision tau2427 contact2427 logTwoBall

theorem center_sq2427 : (center2427.re : ℝ)^2 +
    (center2427.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2427]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2427 : work2427.theta.ok = true ∧
    work2427.jac.invOK = true ∧ acceptsUnitSq work2427.out = true := by decide +kernel

def cell2427 : CellCertificate where
  tauBall := tau2427
  contactCenter := center2427
  contactBall := contact2427
  work := work2427
  center_sq := center_sq2427
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2427.1
  jac_ok := checks2427.2.1
  accepted := checks2427.2.2

def tau2428 : RatBall :=
  ⟨⟨69/320, 93/320⟩, 3/640⟩
def center2428 : GaussianRat :=
  ⟨32008397/200000000, 245849/1250000⟩
def contact2428 : RatBall := localContactBall tau2428 center2428
def work2428 : RoundedTauEval :=
  evalTau precision tau2428 contact2428 logTwoBall

theorem center_sq2428 : (center2428.re : ℝ)^2 +
    (center2428.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2428]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2428 : work2428.theta.ok = true ∧
    work2428.jac.invOK = true ∧ acceptsUnitSq work2428.out = true := by decide +kernel

def cell2428 : CellCertificate where
  tauBall := tau2428
  contactCenter := center2428
  contactBall := contact2428
  work := work2428
  center_sq := center_sq2428
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2428.1
  jac_ok := checks2428.2.1
  accepted := checks2428.2.2

def tau2429 : RatBall :=
  ⟨⟨71/320, 93/320⟩, 3/640⟩
def center2429 : GaussianRat :=
  ⟨82231753/500000000, 98036117/500000000⟩
def contact2429 : RatBall := localContactBall tau2429 center2429
def work2429 : RoundedTauEval :=
  evalTau precision tau2429 contact2429 logTwoBall

theorem center_sq2429 : (center2429.re : ℝ)^2 +
    (center2429.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2429]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2429 : work2429.theta.ok = true ∧
    work2429.jac.invOK = true ∧ acceptsUnitSq work2429.out = true := by decide +kernel

def cell2429 : CellCertificate where
  tauBall := tau2429
  contactCenter := center2429
  contactBall := contact2429
  work := work2429
  center_sq := center_sq2429
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2429.1
  jac_ok := checks2429.2.1
  accepted := checks2429.2.2

def tau2430 : RatBall :=
  ⟨⟨69/320, 19/64⟩, 3/640⟩
def center2430 : GaussianRat :=
  ⟨80325427/500000000, 201116047/1000000000⟩
def contact2430 : RatBall := localContactBall tau2430 center2430
def work2430 : RoundedTauEval :=
  evalTau precision tau2430 contact2430 logTwoBall

theorem center_sq2430 : (center2430.re : ℝ)^2 +
    (center2430.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2430]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2430 : work2430.theta.ok = true ∧
    work2430.jac.invOK = true ∧ acceptsUnitSq work2430.out = true := by decide +kernel

def cell2430 : CellCertificate where
  tauBall := tau2430
  contactCenter := center2430
  contactBall := contact2430
  work := work2430
  center_sq := center_sq2430
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2430.1
  jac_ok := checks2430.2.1
  accepted := checks2430.2.2

def tau2431 : RatBall :=
  ⟨⟨71/320, 19/64⟩, 3/640⟩
def center2431 : GaussianRat :=
  ⟨165085801/1000000000, 40098349/200000000⟩
def contact2431 : RatBall := localContactBall tau2431 center2431
def work2431 : RoundedTauEval :=
  evalTau precision tau2431 contact2431 logTwoBall

theorem center_sq2431 : (center2431.re : ℝ)^2 +
    (center2431.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2431]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2431 : work2431.theta.ok = true ∧
    work2431.jac.invOK = true ∧ acceptsUnitSq work2431.out = true := by decide +kernel

def cell2431 : CellCertificate where
  tauBall := tau2431
  contactCenter := center2431
  contactBall := contact2431
  work := work2431
  center_sq := center_sq2431
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2431.1
  jac_ok := checks2431.2.1
  accepted := checks2431.2.2

def cells : List CellCertificate := [cell2424, cell2425, cell2426, cell2427, cell2428, cell2429, cell2430, cell2431]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303

end


