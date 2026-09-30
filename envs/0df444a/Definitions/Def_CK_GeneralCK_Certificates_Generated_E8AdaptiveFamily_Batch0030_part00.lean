-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0030_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:08:32.087818+00:00
-- url     : https://prove2.me/theorems/e6eb11d7-138d-4ea2-9f36-4084cee93464
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030 (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0030 (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0240 : RatBall :=
  ⟨⟨-13/80, 13/80⟩, 3/160⟩
def center0240 : GaussianRat :=
  ⟨-114628827/1000000000, 110510723/1000000000⟩
def contact0240 : RatBall := localContactBall tau0240 center0240
def work0240 : RoundedTauEval :=
  evalTau precision tau0240 contact0240 logTwoBall

theorem center_sq0240 : (center0240.re : ℝ)^2 +
    (center0240.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0240]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0240 : work0240.theta.ok = true ∧
    work0240.jac.invOK = true ∧ acceptsUnitSq work0240.out = true := by decide +kernel

def cell0240 : CellCertificate where
  tauBall := tau0240
  contactCenter := center0240
  contactBall := contact0240
  work := work0240
  center_sq := center_sq0240
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0240.1
  jac_ok := checks0240.2.1
  accepted := checks0240.2.2

def tau0241 : RatBall :=
  ⟨⟨-3/16, 3/16⟩, 3/160⟩
def center0241 : GaussianRat :=
  ⟨-132989007/1000000000, 15833617/125000000⟩
def contact0241 : RatBall := localContactBall tau0241 center0241
def work0241 : RoundedTauEval :=
  evalTau precision tau0241 contact0241 logTwoBall

theorem center_sq0241 : (center0241.re : ℝ)^2 +
    (center0241.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0241]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0241 : work0241.theta.ok = true ∧
    work0241.jac.invOK = true ∧ acceptsUnitSq work0241.out = true := by decide +kernel

def cell0241 : CellCertificate where
  tauBall := tau0241
  contactCenter := center0241
  contactBall := contact0241
  work := work0241
  center_sq := center_sq0241
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0241.1
  jac_ok := checks0241.2.1
  accepted := checks0241.2.2

def tau0242 : RatBall :=
  ⟨⟨-13/80, 3/16⟩, 3/160⟩
def center0242 : GaussianRat :=
  ⟨-115659239/1000000000, 127856533/1000000000⟩
def contact0242 : RatBall := localContactBall tau0242 center0242
def work0242 : RoundedTauEval :=
  evalTau precision tau0242 contact0242 logTwoBall

theorem center_sq0242 : (center0242.re : ℝ)^2 +
    (center0242.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0242]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0242 : work0242.theta.ok = true ∧
    work0242.jac.invOK = true ∧ acceptsUnitSq work0242.out = true := by decide +kernel

def cell0242 : CellCertificate where
  tauBall := tau0242
  contactCenter := center0242
  contactBall := contact0242
  work := work0242
  center_sq := center_sq0242
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0242.1
  jac_ok := checks0242.2.1
  accepted := checks0242.2.2

def tau0243 : RatBall :=
  ⟨⟨-11/80, 13/80⟩, 3/160⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030


