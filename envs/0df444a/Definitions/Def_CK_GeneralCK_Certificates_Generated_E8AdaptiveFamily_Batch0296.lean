-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0296
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0296
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:32:36.3697+00:00
-- url     : https://prove2.me/theorems/0269350d-9e0b-4697-97dc-1174c1d42e54
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0296.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2368 : RatBall :=
  ⟨⟨49/320, 21/64⟩, 3/640⟩
def center2368 : GaussianRat :=
  ⟨58953523/500000000, 57439977/250000000⟩
def contact2368 : RatBall := localContactBall tau2368 center2368
def work2368 : RoundedTauEval :=
  evalTau precision tau2368 contact2368 logTwoBall

theorem center_sq2368 : (center2368.re : ℝ)^2 +
    (center2368.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2368]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2368 : work2368.theta.ok = true ∧
    work2368.jac.invOK = true ∧ acceptsUnitSq work2368.out = true := by decide +kernel

def cell2368 : CellCertificate where
  tauBall := tau2368
  contactCenter := center2368
  contactBall := contact2368
  work := work2368
  center_sq := center_sq2368
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2368.1
  jac_ok := checks2368.2.1
  accepted := checks2368.2.2

def tau2369 : RatBall :=
  ⟨⟨51/320, 21/64⟩, 3/640⟩
def center2369 : GaussianRat :=
  ⟨122586619/1000000000, 229215321/1000000000⟩
def contact2369 : RatBall := localContactBall tau2369 center2369
def work2369 : RoundedTauEval :=
  evalTau precision tau2369 contact2369 logTwoBall

theorem center_sq2369 : (center2369.re : ℝ)^2 +
    (center2369.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2369]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2369 : work2369.theta.ok = true ∧
    work2369.jac.invOK = true ∧ acceptsUnitSq work2369.out = true := by decide +kernel

def cell2369 : CellCertificate where
  tauBall := tau2369
  contactCenter := center2369
  contactBall := contact2369
  work := work2369
  center_sq := center_sq2369
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2369.1
  jac_ok := checks2369.2.1
  accepted := checks2369.2.2

def tau2370 : RatBall :=
  ⟨⟨49/320, 107/320⟩, 3/640⟩
def center2370 : GaussianRat :=
  ⟨5922481/50000000, 234456553/1000000000⟩
def contact2370 : RatBall := localContactBall tau2370 center2370
def work2370 : RoundedTauEval :=
  evalTau precision tau2370 contact2370 logTwoBall

theorem center_sq2370 : (center2370.re : ℝ)^2 +
    (center2370.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2370 : work2370.theta.ok = true ∧
    work2370.jac.invOK = true ∧ acceptsUnitSq work2370.out = true := by decide +kernel

def cell2370 : CellCertificate where
  tauBall := tau2370
  contactCenter := center2370
  contactBall := contact2370
  work := work2370
  center_sq := center_sq2370
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2370.1
  jac_ok := checks2370.2.1
  accepted := checks2370.2.2

def tau2371 : RatBall :=
  ⟨⟨51/320, 107/320⟩, 3/640⟩
def center2371 : GaussianRat :=
  ⟨24629661/200000000, 233896771/1000000000⟩
def contact2371 : RatBall := localContactBall tau2371 center2371
def work2371 : RoundedTauEval :=
  evalTau precision tau2371 contact2371 logTwoBall

theorem center_sq2371 : (center2371.re : ℝ)^2 +
    (center2371.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2371]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2371 : work2371.theta.ok = true ∧
    work2371.jac.invOK = true ∧ acceptsUnitSq work2371.out = true := by decide +kernel

def cell2371 : CellCertificate where
  tauBall := tau2371
  contactCenter := center2371
  contactBall := contact2371
  work := work2371
  center_sq := center_sq2371
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2371.1
  jac_ok := checks2371.2.1
  accepted := checks2371.2.2

def tau2372 : RatBall :=
  ⟨⟨53/320, 21/64⟩, 3/640⟩
def center2372 : GaussianRat :=
  ⟨127250921/1000000000, 228652029/1000000000⟩
def contact2372 : RatBall := localContactBall tau2372 center2372
def work2372 : RoundedTauEval :=
  evalTau precision tau2372 contact2372 logTwoBall

theorem center_sq2372 : (center2372.re : ℝ)^2 +
    (center2372.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2372]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2372 : work2372.theta.ok = true ∧
    work2372.jac.invOK = true ∧ acceptsUnitSq work2372.out = true := by decide +kernel

def cell2372 : CellCertificate where
  tauBall := tau2372
  contactCenter := center2372
  contactBall := contact2372
  work := work2372
  center_sq := center_sq2372
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2372.1
  jac_ok := checks2372.2.1
  accepted := checks2372.2.2

def tau2373 : RatBall :=
  ⟨⟨11/64, 21/64⟩, 3/640⟩
def center2373 : GaussianRat :=
  ⟨65949739/500000000, 57017591/250000000⟩
def contact2373 : RatBall := localContactBall tau2373 center2373
def work2373 : RoundedTauEval :=
  evalTau precision tau2373 contact2373 logTwoBall

theorem center_sq2373 : (center2373.re : ℝ)^2 +
    (center2373.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2373]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2373 : work2373.theta.ok = true ∧
    work2373.jac.invOK = true ∧ acceptsUnitSq work2373.out = true := by decide +kernel

def cell2373 : CellCertificate where
  tauBall := tau2373
  contactCenter := center2373
  contactBall := contact2373
  work := work2373
  center_sq := center_sq2373
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2373.1
  jac_ok := checks2373.2.1
  accepted := checks2373.2.2

def tau2374 : RatBall :=
  ⟨⟨53/320, 107/320⟩, 3/640⟩
def center2374 : GaussianRat :=
  ⟨15978923/125000000, 233317801/1000000000⟩
def contact2374 : RatBall := localContactBall tau2374 center2374
def work2374 : RoundedTauEval :=
  evalTau precision tau2374 contact2374 logTwoBall

theorem center_sq2374 : (center2374.re : ℝ)^2 +
    (center2374.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2374]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2374 : work2374.theta.ok = true ∧
    work2374.jac.invOK = true ∧ acceptsUnitSq work2374.out = true := by decide +kernel

def cell2374 : CellCertificate where
  tauBall := tau2374
  contactCenter := center2374
  contactBall := contact2374
  work := work2374
  center_sq := center_sq2374
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2374.1
  jac_ok := checks2374.2.1
  accepted := checks2374.2.2

def tau2375 : RatBall :=
  ⟨⟨11/64, 107/320⟩, 3/640⟩
def center2375 : GaussianRat :=
  ⟨66249189/500000000, 232719989/1000000000⟩
def contact2375 : RatBall := localContactBall tau2375 center2375
def work2375 : RoundedTauEval :=
  evalTau precision tau2375 contact2375 logTwoBall

theorem center_sq2375 : (center2375.re : ℝ)^2 +
    (center2375.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2375]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2375 : work2375.theta.ok = true ∧
    work2375.jac.invOK = true ∧ acceptsUnitSq work2375.out = true := by decide +kernel

def cell2375 : CellCertificate where
  tauBall := tau2375
  contactCenter := center2375
  contactBall := contact2375
  work := work2375
  center_sq := center_sq2375
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2375.1
  jac_ok := checks2375.2.1
  accepted := checks2375.2.2

def cells : List CellCertificate := [cell2368, cell2369, cell2370, cell2371, cell2372, cell2373, cell2374, cell2375]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296

end


