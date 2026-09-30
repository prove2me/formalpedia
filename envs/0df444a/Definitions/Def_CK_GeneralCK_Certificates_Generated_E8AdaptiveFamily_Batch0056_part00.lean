-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0056_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T14:19:03.197029+00:00
-- url     : https://prove2.me/theorems/f324b02d-ab8f-4063-93e0-54b3960bdb4b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0056 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0448 : RatBall :=
  ⟨⟨-5/32, -41/160⟩, 3/320⟩
def center0448 : GaussianRat :=
  ⟨-114906151/1000000000, -176804909/1000000000⟩
def contact0448 : RatBall := localContactBall tau0448 center0448
def work0448 : RoundedTauEval :=
  evalTau precision tau0448 contact0448 logTwoBall

theorem center_sq0448 : (center0448.re : ℝ)^2 +
    (center0448.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0448]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0448 : work0448.theta.ok = true ∧
    work0448.jac.invOK = true ∧ acceptsUnitSq work0448.out = true := by decide +kernel

def cell0448 : CellCertificate where
  tauBall := tau0448
  contactCenter := center0448
  contactBall := contact0448
  work := work0448
  center_sq := center_sq0448
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0448.1
  jac_ok := checks0448.2.1
  accepted := checks0448.2.2

def tau0449 : RatBall :=
  ⟨⟨-23/160, -47/160⟩, 3/320⟩
def center0449 : GaussianRat :=
  ⟨-108280123/1000000000, -204924443/1000000000⟩
def contact0449 : RatBall := localContactBall tau0449 center0449
def work0449 : RoundedTauEval :=
  evalTau precision tau0449 contact0449 logTwoBall

theorem center_sq0449 : (center0449.re : ℝ)^2 +
    (center0449.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0449]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0449 : work0449.theta.ok = true ∧
    work0449.jac.invOK = true ∧ acceptsUnitSq work0449.out = true := by decide +kernel

def cell0449 : CellCertificate where
  tauBall := tau0449
  contactCenter := center0449
  contactBall := contact0449
  work := work0449
  center_sq := center_sq0449
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0449.1
  jac_ok := checks0449.2.1
  accepted := checks0449.2.2

def tau0450 : RatBall :=
  ⟨⟨-21/160, -47/160⟩, 3/320⟩
def center0450 : GaussianRat :=
  ⟨-618987/6250000, -102878573/500000000⟩
def contact0450 : RatBall := localContactBall tau0450 center0450
def work0450 : RoundedTauEval :=
  evalTau precision tau0450 contact0450 logTwoBall

theorem center_sq0450 : (center0450.re : ℝ)^2 +
    (center0450.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0450]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0450 : work0450.theta.ok = true ∧
    work0450.jac.invOK = true ∧ acceptsUnitSq work0450.out = true := by decide +kernel

def cell0450 : CellCertificate where
  tauBall := tau0450
  contactCenter := center0450
  contactBall := contact0450
  work := work0450
  center_sq := center_sq0450
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0450.1
  jac_ok := checks0450.2.1
  accepted := checks0450.2.2

def tau0451 : RatBall :=
  ⟨⟨-23/160, -9/32⟩, 3/320⟩
def center0451 : GaussianRat :=
  ⟨-107438161/1000000000, -195739697/1000000000⟩
def contact0451 : RatBall := localContactBall tau0451 center0451
def work0451 : RoundedTauEval :=
  evalTau precision tau0451 contact0451 logTwoBall

theorem center_sq0451 : (center0451.re : ℝ)^2 +
    (center0451.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0451]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0451 : work0451.theta.ok = true ∧
    work0451.jac.invOK = true ∧ acceptsUnitSq work0451.out = true := by decide +kernel

def cell0451 : CellCertificate where
  tauBall := tau0451
  contactCenter := center0451
  contactBall := contact0451
  work := work0451
  center_sq := center_sq0451
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0451.1
  jac_ok := checks0451.2.1
  accepted := checks0451.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056


