-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0061
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0061
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:43:58.164764+00:00
-- url     : https://prove2.me/theorems/c8d8a46a-f904-4c48-9f40-1c32908c332d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0061.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0488 : RatBall :=
  ⟨⟨-11/32, -29/160⟩, 3/320⟩
def center0488 : GaussianRat :=
  ⟨-117898859/500000000, -112506293/1000000000⟩
def contact0488 : RatBall := localContactBall tau0488 center0488
def work0488 : RoundedTauEval :=
  evalTau precision tau0488 contact0488 logTwoBall

theorem center_sq0488 : (center0488.re : ℝ)^2 +
    (center0488.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0488]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0488 : work0488.theta.ok = true ∧
    work0488.jac.invOK = true ∧ acceptsUnitSq work0488.out = true := by decide +kernel

def cell0488 : CellCertificate where
  tauBall := tau0488
  contactCenter := center0488
  contactBall := contact0488
  work := work0488
  center_sq := center_sq0488
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0488.1
  jac_ok := checks0488.2.1
  accepted := checks0488.2.2

def tau0489 : RatBall :=
  ⟨⟨-53/160, -29/160⟩, 3/320⟩
def center0489 : GaussianRat :=
  ⟨-227914773/1000000000, -56716957/500000000⟩
def contact0489 : RatBall := localContactBall tau0489 center0489
def work0489 : RoundedTauEval :=
  evalTau precision tau0489 contact0489 logTwoBall

theorem center_sq0489 : (center0489.re : ℝ)^2 +
    (center0489.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0489]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0489 : work0489.theta.ok = true ∧
    work0489.jac.invOK = true ∧ acceptsUnitSq work0489.out = true := by decide +kernel

def cell0489 : CellCertificate where
  tauBall := tau0489
  contactCenter := center0489
  contactBall := contact0489
  work := work0489
  center_sq := center_sq0489
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0489.1
  jac_ok := checks0489.2.1
  accepted := checks0489.2.2

def tau0490 : RatBall :=
  ⟨⟨-51/160, -31/160⟩, 3/320⟩
def center0490 : GaussianRat :=
  ⟨-110447247/500000000, -61169673/500000000⟩
def contact0490 : RatBall := localContactBall tau0490 center0490
def work0490 : RoundedTauEval :=
  evalTau precision tau0490 contact0490 logTwoBall

theorem center_sq0490 : (center0490.re : ℝ)^2 +
    (center0490.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0490]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0490 : work0490.theta.ok = true ∧
    work0490.jac.invOK = true ∧ acceptsUnitSq work0490.out = true := by decide +kernel

def cell0490 : CellCertificate where
  tauBall := tau0490
  contactCenter := center0490
  contactBall := contact0490
  work := work0490
  center_sq := center_sq0490
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0490.1
  jac_ok := checks0490.2.1
  accepted := checks0490.2.2

def tau0491 : RatBall :=
  ⟨⟨-49/160, -31/160⟩, 3/320⟩
def center0491 : GaussianRat :=
  ⟨-106425859/500000000, -123294587/1000000000⟩
def contact0491 : RatBall := localContactBall tau0491 center0491
def work0491 : RoundedTauEval :=
  evalTau precision tau0491 contact0491 logTwoBall

theorem center_sq0491 : (center0491.re : ℝ)^2 +
    (center0491.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0491]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0491 : work0491.theta.ok = true ∧
    work0491.jac.invOK = true ∧ acceptsUnitSq work0491.out = true := by decide +kernel

def cell0491 : CellCertificate where
  tauBall := tau0491
  contactCenter := center0491
  contactBall := contact0491
  work := work0491
  center_sq := center_sq0491
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0491.1
  jac_ok := checks0491.2.1
  accepted := checks0491.2.2

def tau0492 : RatBall :=
  ⟨⟨-51/160, -29/160⟩, 3/320⟩
def center0492 : GaussianRat :=
  ⟨-429614/1953125, -114341983/1000000000⟩
def contact0492 : RatBall := localContactBall tau0492 center0492
def work0492 : RoundedTauEval :=
  evalTau precision tau0492 contact0492 logTwoBall

theorem center_sq0492 : (center0492.re : ℝ)^2 +
    (center0492.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0492]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0492 : work0492.theta.ok = true ∧
    work0492.jac.invOK = true ∧ acceptsUnitSq work0492.out = true := by decide +kernel

def cell0492 : CellCertificate where
  tauBall := tau0492
  contactCenter := center0492
  contactBall := contact0492
  work := work0492
  center_sq := center_sq0492
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0492.1
  jac_ok := checks0492.2.1
  accepted := checks0492.2.2

def tau0493 : RatBall :=
  ⟨⟨-49/160, -29/160⟩, 3/320⟩
def center0493 : GaussianRat :=
  ⟨-52985469/250000000, -115229173/1000000000⟩
def contact0493 : RatBall := localContactBall tau0493 center0493
def work0493 : RoundedTauEval :=
  evalTau precision tau0493 contact0493 logTwoBall

theorem center_sq0493 : (center0493.re : ℝ)^2 +
    (center0493.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0493]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0493 : work0493.theta.ok = true ∧
    work0493.jac.invOK = true ∧ acceptsUnitSq work0493.out = true := by decide +kernel

def cell0493 : CellCertificate where
  tauBall := tau0493
  contactCenter := center0493
  contactBall := contact0493
  work := work0493
  center_sq := center_sq0493
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0493.1
  jac_ok := checks0493.2.1
  accepted := checks0493.2.2

def tau0494 : RatBall :=
  ⟨⟨-11/32, -27/160⟩, 3/320⟩
def center0494 : GaussianRat :=
  ⟨-234895911/1000000000, -52333711/500000000⟩
def contact0494 : RatBall := localContactBall tau0494 center0494
def work0494 : RoundedTauEval :=
  evalTau precision tau0494 contact0494 logTwoBall

theorem center_sq0494 : (center0494.re : ℝ)^2 +
    (center0494.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0494]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0494 : work0494.theta.ok = true ∧
    work0494.jac.invOK = true ∧ acceptsUnitSq work0494.out = true := by decide +kernel

def cell0494 : CellCertificate where
  tauBall := tau0494
  contactCenter := center0494
  contactBall := contact0494
  work := work0494
  center_sq := center_sq0494
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0494.1
  jac_ok := checks0494.2.1
  accepted := checks0494.2.2

def tau0495 : RatBall :=
  ⟨⟨-53/160, -27/160⟩, 3/320⟩
def center0495 : GaussianRat :=
  ⟨-113515613/500000000, -13190697/125000000⟩
def contact0495 : RatBall := localContactBall tau0495 center0495
def work0495 : RoundedTauEval :=
  evalTau precision tau0495 contact0495 logTwoBall

theorem center_sq0495 : (center0495.re : ℝ)^2 +
    (center0495.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0495]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0495 : work0495.theta.ok = true ∧
    work0495.jac.invOK = true ∧ acceptsUnitSq work0495.out = true := by decide +kernel

def cell0495 : CellCertificate where
  tauBall := tau0495
  contactCenter := center0495
  contactBall := contact0495
  work := work0495
  center_sq := center_sq0495
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0495.1
  jac_ok := checks0495.2.1
  accepted := checks0495.2.2

def cells : List CellCertificate := [cell0488, cell0489, cell0490, cell0491, cell0492, cell0493, cell0494, cell0495]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061

end


