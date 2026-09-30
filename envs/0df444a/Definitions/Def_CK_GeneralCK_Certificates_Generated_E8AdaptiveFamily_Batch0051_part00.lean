-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0051_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:59:01.19527+00:00
-- url     : https://prove2.me/theorems/10c55d8a-4d43-428e-88f6-9cfbbec82435
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0051 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0408 : RatBall :=
  ⟨⟨-9/160, -53/160⟩, 3/320⟩
def center0408 : GaussianRat :=
  ⟨-43918333/1000000000, -238021713/1000000000⟩
def contact0408 : RatBall := localContactBall tau0408 center0408
def work0408 : RoundedTauEval :=
  evalTau precision tau0408 contact0408 logTwoBall

theorem center_sq0408 : (center0408.re : ℝ)^2 +
    (center0408.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0408]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0408 : work0408.theta.ok = true ∧
    work0408.jac.invOK = true ∧ acceptsUnitSq work0408.out = true := by decide +kernel

def cell0408 : CellCertificate where
  tauBall := tau0408
  contactCenter := center0408
  contactBall := contact0408
  work := work0408
  center_sq := center_sq0408
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0408.1
  jac_ok := checks0408.2.1
  accepted := checks0408.2.2

def tau0409 : RatBall :=
  ⟨⟨-3/32, -51/160⟩, 3/320⟩
def center0409 : GaussianRat :=
  ⟨-18071427/250000000, -113380411/500000000⟩
def contact0409 : RatBall := localContactBall tau0409 center0409
def work0409 : RoundedTauEval :=
  evalTau precision tau0409 contact0409 logTwoBall

theorem center_sq0409 : (center0409.re : ℝ)^2 +
    (center0409.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0409]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0409 : work0409.theta.ok = true ∧
    work0409.jac.invOK = true ∧ acceptsUnitSq work0409.out = true := by decide +kernel

def cell0409 : CellCertificate where
  tauBall := tau0409
  contactCenter := center0409
  contactBall := contact0409
  work := work0409
  center_sq := center_sq0409
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0409.1
  jac_ok := checks0409.2.1
  accepted := checks0409.2.2

def tau0410 : RatBall :=
  ⟨⟨-13/160, -51/160⟩, 3/320⟩
def center0410 : GaussianRat :=
  ⟨-2508961/40000000, -56843321/250000000⟩
def contact0410 : RatBall := localContactBall tau0410 center0410
def work0410 : RoundedTauEval :=
  evalTau precision tau0410 contact0410 logTwoBall

theorem center_sq0410 : (center0410.re : ℝ)^2 +
    (center0410.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0410]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0410 : work0410.theta.ok = true ∧
    work0410.jac.invOK = true ∧ acceptsUnitSq work0410.out = true := by decide +kernel

def cell0410 : CellCertificate where
  tauBall := tau0410
  contactCenter := center0410
  contactBall := contact0410
  work := work0410
  center_sq := center_sq0410
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0410.1
  jac_ok := checks0410.2.1
  accepted := checks0410.2.2

def tau0411 : RatBall :=
  ⟨⟨-3/32, -49/160⟩, 3/320⟩
def center0411 : GaussianRat :=
  ⟨-14329959/200000000, -108628837/500000000⟩
def contact0411 : RatBall := localContactBall tau0411 center0411
def work0411 : RoundedTauEval :=
  evalTau precision tau0411 contact0411 logTwoBall

theorem center_sq0411 : (center0411.re : ℝ)^2 +
    (center0411.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0411]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0411 : work0411.theta.ok = true ∧
    work0411.jac.invOK = true ∧ acceptsUnitSq work0411.out = true := by decide +kernel

def cell0411 : CellCertificate where
  tauBall := tau0411
  contactCenter := center0411
  contactBall := contact0411
  work := work0411
  center_sq := center_sq0411
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0411.1
  jac_ok := checks0411.2.1
  accepted := checks0411.2.2

def tau0412 : RatBall :=
  ⟨⟨-13/160, -49/160⟩, 3/320⟩
def center0412 : GaussianRat :=
  ⟨-3885599/62500000, -6807377/31250000⟩
def contact0412 : RatBall := localContactBall tau0412 center0412
def work0412 : RoundedTauEval :=
  evalTau precision tau0412 contact0412 logTwoBall

theorem center_sq0412 : (center0412.re : ℝ)^2 +
    (center0412.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0412]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051


