-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0066
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0066
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:05:29.497398+00:00
-- url     : https://prove2.me/theorems/bac48b09-a3bc-45c8-8bbf-df6776627bf5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0066.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0528 : RatBall :=
  ⟨⟨-47/160, -29/160⟩, 3/320⟩
def center0528 : GaussianRat :=
  ⟨-25481847/125000000, -58047077/500000000⟩
def contact0528 : RatBall := localContactBall tau0528 center0528
def work0528 : RoundedTauEval :=
  evalTau precision tau0528 contact0528 logTwoBall

theorem center_sq0528 : (center0528.re : ℝ)^2 +
    (center0528.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0528]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0528 : work0528.theta.ok = true ∧
    work0528.jac.invOK = true ∧ acceptsUnitSq work0528.out = true := by decide +kernel

def cell0528 : CellCertificate where
  tauBall := tau0528
  contactCenter := center0528
  contactBall := contact0528
  work := work0528
  center_sq := center_sq0528
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0528.1
  jac_ok := checks0528.2.1
  accepted := checks0528.2.2

def tau0529 : RatBall :=
  ⟨⟨-9/32, -29/160⟩, 3/320⟩
def center0529 : GaussianRat :=
  ⟨-97851331/500000000, -116935591/1000000000⟩
def contact0529 : RatBall := localContactBall tau0529 center0529
def work0529 : RoundedTauEval :=
  evalTau precision tau0529 contact0529 logTwoBall

theorem center_sq0529 : (center0529.re : ℝ)^2 +
    (center0529.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0529]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0529 : work0529.theta.ok = true ∧
    work0529.jac.invOK = true ∧ acceptsUnitSq work0529.out = true := by decide +kernel

def cell0529 : CellCertificate where
  tauBall := tau0529
  contactCenter := center0529
  contactBall := contact0529
  work := work0529
  center_sq := center_sq0529
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0529.1
  jac_ok := checks0529.2.1
  accepted := checks0529.2.2

def tau0530 : RatBall :=
  ⟨⟨-43/160, -31/160⟩, 3/320⟩
def center0530 : GaussianRat :=
  ⟨-188321901/1000000000, -126012049/1000000000⟩
def contact0530 : RatBall := localContactBall tau0530 center0530
def work0530 : RoundedTauEval :=
  evalTau precision tau0530 contact0530 logTwoBall

theorem center_sq0530 : (center0530.re : ℝ)^2 +
    (center0530.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0530]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0530 : work0530.theta.ok = true ∧
    work0530.jac.invOK = true ∧ acceptsUnitSq work0530.out = true := by decide +kernel

def cell0530 : CellCertificate where
  tauBall := tau0530
  contactCenter := center0530
  contactBall := contact0530
  work := work0530
  center_sq := center_sq0530
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0530.1
  jac_ok := checks0530.2.1
  accepted := checks0530.2.2

def tau0531 : RatBall :=
  ⟨⟨-41/160, -31/160⟩, 3/320⟩
def center0531 : GaussianRat :=
  ⟨-36003433/200000000, -3171591/25000000⟩
def contact0531 : RatBall := localContactBall tau0531 center0531
def work0531 : RoundedTauEval :=
  evalTau precision tau0531 contact0531 logTwoBall

theorem center_sq0531 : (center0531.re : ℝ)^2 +
    (center0531.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0531]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0531 : work0531.theta.ok = true ∧
    work0531.jac.invOK = true ∧ acceptsUnitSq work0531.out = true := by decide +kernel

def cell0531 : CellCertificate where
  tauBall := tau0531
  contactCenter := center0531
  contactBall := contact0531
  work := work0531
  center_sq := center_sq0531
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0531.1
  jac_ok := checks0531.2.1
  accepted := checks0531.2.2

def tau0532 : RatBall :=
  ⟨⟨-43/160, -29/160⟩, 3/320⟩
def center0532 : GaussianRat :=
  ⟨-187487239/1000000000, -23550431/200000000⟩
def contact0532 : RatBall := localContactBall tau0532 center0532
def work0532 : RoundedTauEval :=
  evalTau precision tau0532 contact0532 logTwoBall

theorem center_sq0532 : (center0532.re : ℝ)^2 +
    (center0532.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0532]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0532 : work0532.theta.ok = true ∧
    work0532.jac.invOK = true ∧ acceptsUnitSq work0532.out = true := by decide +kernel

def cell0532 : CellCertificate where
  tauBall := tau0532
  contactCenter := center0532
  contactBall := contact0532
  work := work0532
  center_sq := center_sq0532
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0532.1
  jac_ok := checks0532.2.1
  accepted := checks0532.2.2

def tau0533 : RatBall :=
  ⟨⟨-41/160, -29/160⟩, 3/320⟩
def center0533 : GaussianRat :=
  ⟨-89605161/500000000, -4741701/40000000⟩
def contact0533 : RatBall := localContactBall tau0533 center0533
def work0533 : RoundedTauEval :=
  evalTau precision tau0533 contact0533 logTwoBall

theorem center_sq0533 : (center0533.re : ℝ)^2 +
    (center0533.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0533]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0533 : work0533.theta.ok = true ∧
    work0533.jac.invOK = true ∧ acceptsUnitSq work0533.out = true := by decide +kernel

def cell0533 : CellCertificate where
  tauBall := tau0533
  contactCenter := center0533
  contactBall := contact0533
  work := work0533
  center_sq := center_sq0533
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0533.1
  jac_ok := checks0533.2.1
  accepted := checks0533.2.2

def tau0534 : RatBall :=
  ⟨⟨-47/160, -27/160⟩, 3/320⟩
def center0534 : GaussianRat :=
  ⟨-5075841/25000000, -107985769/1000000000⟩
def contact0534 : RatBall := localContactBall tau0534 center0534
def work0534 : RoundedTauEval :=
  evalTau precision tau0534 contact0534 logTwoBall

theorem center_sq0534 : (center0534.re : ℝ)^2 +
    (center0534.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0534]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0534 : work0534.theta.ok = true ∧
    work0534.jac.invOK = true ∧ acceptsUnitSq work0534.out = true := by decide +kernel

def cell0534 : CellCertificate where
  tauBall := tau0534
  contactCenter := center0534
  contactBall := contact0534
  work := work0534
  center_sq := center_sq0534
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0534.1
  jac_ok := checks0534.2.1
  accepted := checks0534.2.2

def tau0535 : RatBall :=
  ⟨⟨-9/32, -27/160⟩, 3/320⟩
def center0535 : GaussianRat :=
  ⟨-194904883/1000000000, -13595459/125000000⟩
def contact0535 : RatBall := localContactBall tau0535 center0535
def work0535 : RoundedTauEval :=
  evalTau precision tau0535 contact0535 logTwoBall

theorem center_sq0535 : (center0535.re : ℝ)^2 +
    (center0535.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0535]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0535 : work0535.theta.ok = true ∧
    work0535.jac.invOK = true ∧ acceptsUnitSq work0535.out = true := by decide +kernel

def cell0535 : CellCertificate where
  tauBall := tau0535
  contactCenter := center0535
  contactBall := contact0535
  work := work0535
  center_sq := center_sq0535
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0535.1
  jac_ok := checks0535.2.1
  accepted := checks0535.2.2

def cells : List CellCertificate := [cell0528, cell0529, cell0530, cell0531, cell0532, cell0533, cell0534, cell0535]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066

end


