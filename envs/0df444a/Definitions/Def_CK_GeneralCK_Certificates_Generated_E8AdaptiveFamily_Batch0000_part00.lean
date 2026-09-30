-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0000_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0000_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:40.056805+00:00
-- url     : https://prove2.me/theorems/f3c763ec-44f6-446f-9ed2-9645170527e2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0000 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0000 : RatBall :=
  ⟨⟨-9/40, -1/40⟩, 3/80⟩
def center0000 : GaussianRat :=
  ⟨-76697679/500000000, -4116037/250000000⟩
def contact0000 : RatBall := localContactBall tau0000 center0000
def work0000 : RoundedTauEval :=
  evalTau precision tau0000 contact0000 logTwoBall

theorem center_sq0000 : (center0000.re : ℝ)^2 +
    (center0000.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0000]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0000 : work0000.theta.ok = true ∧
    work0000.jac.invOK = true ∧ acceptsUnitSq work0000.out = true := by decide +kernel

def cell0000 : CellCertificate where
  tauBall := tau0000
  contactCenter := center0000
  contactBall := contact0000
  work := work0000
  center_sq := center_sq0000
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0000.1
  jac_ok := checks0000.2.1
  accepted := checks0000.2.2

def tau0001 : RatBall :=
  ⟨⟨-1/8, -1/8⟩, 3/80⟩
def center0001 : GaussianRat :=
  ⟨-87563403/1000000000, -85687457/1000000000⟩
def contact0001 : RatBall := localContactBall tau0001 center0001
def work0001 : RoundedTauEval :=
  evalTau precision tau0001 contact0001 logTwoBall

theorem center_sq0001 : (center0001.re : ℝ)^2 +
    (center0001.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0001]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0001 : work0001.theta.ok = true ∧
    work0001.jac.invOK = true ∧ acceptsUnitSq work0001.out = true := by decide +kernel

def cell0001 : CellCertificate where
  tauBall := tau0001
  contactCenter := center0001
  contactBall := contact0001
  work := work0001
  center_sq := center_sq0001
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0001.1
  jac_ok := checks0001.2.1
  accepted := checks0001.2.2

def tau0002 : RatBall :=
  ⟨⟨-1/40, -7/40⟩, 3/80⟩
def center0002 : GaussianRat :=
  ⟨-17893761/1000000000, -7658063/62500000⟩
def contact0002 : RatBall := localContactBall tau0002 center0002
def work0002 : RoundedTauEval :=
  evalTau precision tau0002 contact0002 logTwoBall

theorem center_sq0002 : (center0002.re : ℝ)^2 +
    (center0002.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0002]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0002 : work0002.theta.ok = true ∧
    work0002.jac.invOK = true ∧ acceptsUnitSq work0002.out = true := by decide +kernel

def cell0002 : CellCertificate where
  tauBall := tau0002
  contactCenter := center0002
  contactBall := contact0002
  work := work0002
  center_sq := center_sq0002
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0002.1
  jac_ok := checks0002.2.1
  accepted := checks0002.2.2

def tau0003 : RatBall :=
  ⟨⟨-3/40, -1/8⟩, 3/80⟩
def center0003 : GaussianRat :=
  ⟨-52733271/1000000000, -10824621/125000000⟩
def contact0003 : RatBall := localContactBall tau0003 center0003
def work0003 : RoundedTauEval :=
  evalTau precision tau0003 contact0003 logTwoBall

theorem center_sq0003 : (center0003.re : ℝ)^2 +
    (center0003.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0003]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0003 : work0003.theta.ok = true ∧
    work0003.jac.invOK = true ∧ acceptsUnitSq work0003.out = true := by decide +kernel

def cell0003 : CellCertificate where
  tauBall := tau0003
  contactCenter := center0003
  contactBall := contact0003
  work := work0003
  center_sq := center_sq0003
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0003.1
  jac_ok := checks0003.2.1
  accepted := checks0003.2.2

def tau0004 : RatBall :=
  ⟨⟨-1/40, -1/8⟩, 3/80⟩
def center0004 : GaussianRat :=
  ⟨-17610637/1000000000, -8705903/100000000⟩
def contact0004 : RatBall := localContactBall tau0004 center0004
def work0004 : RoundedTauEval :=
  evalTau precision tau0004 contact0004 logTwoBall

theorem center_sq0004 : (center0004.re : ℝ)^2 +
    (center0004.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0004]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0004 : work0004.theta.ok = true ∧
    work0004.jac.invOK = true ∧ acceptsUnitSq work0004.out = true := by decide +kernel

def cell0004 : CellCertificate where
  tauBall := tau0004
  contactCenter := center0004
  contactBall := contact0004
  work := work0004
  center_sq := center_sq0004
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0004.1
  jac_ok := checks0004.2.1
  accepted := checks0004.2.2

def tau0005 : RatBall :=
  ⟨⟨-7/40, -3/40⟩, 3/80⟩
def center0005 : GaussianRat :=
  ⟨-7544217/62500000, -12616221/250000000⟩
def contact0005 : RatBall := localContactBall tau0005 center0005
def work0005 : RoundedTauEval :=
  evalTau precision tau0005 contact0005 logTwoBall

theorem center_sq0005 : (center0005.re : ℝ)^2 +
    (center0005.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0005]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0005 : work0005.theta.ok = true ∧
    work0005.jac.invOK = true ∧ acceptsUnitSq work0005.out = true := by decide +kernel

def cell0005 : CellCertificate where
  tauBall := tau0005
  contactCenter := center0005
  contactBall := contact0005
  work := work0005
  center_sq := center_sq0005
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0005.1
  jac_ok := checks0005.2.1
  accepted := checks0005.2.2


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0000


