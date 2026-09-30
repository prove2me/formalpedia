-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0003_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:31:27.956987+00:00
-- url     : https://prove2.me/theorems/ba17bc65-33a5-48c7-b9c4-f5e9beca2bd3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0003 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0024 : RatBall :=
  ⟨⟨7/40, -1/40⟩, 3/80⟩
def center0024 : GaussianRat :=
  ⟨120111093/1000000000, -16796751/1000000000⟩
def contact0024 : RatBall := localContactBall tau0024 center0024
def work0024 : RoundedTauEval :=
  evalTau precision tau0024 contact0024 logTwoBall

theorem center_sq0024 : (center0024.re : ℝ)^2 +
    (center0024.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0024]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0024 : work0024.theta.ok = true ∧
    work0024.jac.invOK = true ∧ acceptsUnitSq work0024.out = true := by decide +kernel

def cell0024 : CellCertificate where
  tauBall := tau0024
  contactCenter := center0024
  contactBall := contact0024
  work := work0024
  center_sq := center_sq0024
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0024.1
  jac_ok := checks0024.2.1
  accepted := checks0024.2.2

def tau0025 : RatBall :=
  ⟨⟨9/40, -1/40⟩, 3/80⟩
def center0025 : GaussianRat :=
  ⟨76697679/500000000, -4116037/250000000⟩
def contact0025 : RatBall := localContactBall tau0025 center0025
def work0025 : RoundedTauEval :=
  evalTau precision tau0025 contact0025 logTwoBall

theorem center_sq0025 : (center0025.re : ℝ)^2 +
    (center0025.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0025]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0025 : work0025.theta.ok = true ∧
    work0025.jac.invOK = true ∧ acceptsUnitSq work0025.out = true := by decide +kernel

def cell0025 : CellCertificate where
  tauBall := tau0025
  contactCenter := center0025
  contactBall := contact0025
  work := work0025
  center_sq := center_sq0025
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0025.1
  jac_ok := checks0025.2.1
  accepted := checks0025.2.2

def tau0026 : RatBall :=
  ⟨⟨-9/40, 1/40⟩, 3/80⟩
def center0026 : GaussianRat :=
  ⟨-76697679/500000000, 4116037/250000000⟩
def contact0026 : RatBall := localContactBall tau0026 center0026
def work0026 : RoundedTauEval :=
  evalTau precision tau0026 contact0026 logTwoBall

theorem center_sq0026 : (center0026.re : ℝ)^2 +
    (center0026.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0026]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0026 : work0026.theta.ok = true ∧
    work0026.jac.invOK = true ∧ acceptsUnitSq work0026.out = true := by decide +kernel

def cell0026 : CellCertificate where
  tauBall := tau0026
  contactCenter := center0026
  contactBall := contact0026
  work := work0026
  center_sq := center_sq0026
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0026.1
  jac_ok := checks0026.2.1
  accepted := checks0026.2.2

def tau0027 : RatBall :=
  ⟨⟨-7/40, 1/40⟩, 3/80⟩
def center0027 : GaussianRat :=
  ⟨-120111093/1000000000, 16796751/1000000000⟩
def contact0027 : RatBall := localContactBall tau0027 center0027
def work0027 : RoundedTauEval :=
  evalTau precision tau0027 contact0027 logTwoBall

theorem center_sq0027 : (center0027.re : ℝ)^2 +
    (center0027.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0027]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0027 : work0027.theta.ok = true ∧
    work0027.jac.invOK = true ∧ acceptsUnitSq work0027.out = true := by decide +kernel

def cell0027 : CellCertificate where
  tauBall := tau0027
  contactCenter := center0027
  contactBall := contact0027
  work := work0027
  center_sq := center_sq0027
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0027.1
  jac_ok := checks0027.2.1
  accepted := checks0027.2.2

def tau0028 : RatBall :=
  ⟨⟨-1/8, 1/40⟩, 3/80⟩
def center0028 : GaussianRat :=
  ⟨-8623323/100000000, 17054997/1000000000⟩
def contact0028 : RatBall := localContactBall tau0028 center0028
def work0028 : RoundedTauEval :=
  evalTau precision tau0028 contact0028 logTwoBall

theorem center_sq0028 : (center0028.re : ℝ)^2 +
    (center0028.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0028]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0028 : work0028.theta.ok = true ∧
    work0028.jac.invOK = true ∧ acceptsUnitSq work0028.out = true := by decide +kernel

def cell0028 : CellCertificate where
  tauBall := tau0028
  contactCenter := center0028
  contactBall := contact0028
  work := work0028
  center_sq := center_sq0028
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0028.1
  jac_ok := checks0028.2.1
  accepted := checks0028.2.2

def tau0029 : RatBall :=
  ⟨⟨-7/40, 3/40⟩, 3/80⟩
def center0029 : GaussianRat :=
  ⟨-7544217/62500000, 12616221/250000000⟩
def contact0029 : RatBall := localContactBall tau0029 center0029
def work0029 : RoundedTauEval :=
  evalTau precision tau0029 contact0029 logTwoBall

theorem center_sq0029 : (center0029.re : ℝ)^2 +
    (center0029.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0029]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0029 : work0029.theta.ok = true ∧
    work0029.jac.invOK = true ∧ acceptsUnitSq work0029.out = true := by decide +kernel

def cell0029 : CellCertificate where
  tauBall := tau0029
  contactCenter := center0029
  contactBall := contact0029
  work := work0029
  center_sq := center_sq0029
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0029.1
  jac_ok := checks0029.2.1
  accepted := checks0029.2.2

def tau0030 : RatBall :=
  ⟨⟨-1/8, 3/40⟩, 3/80⟩
def center0030 : GaussianRat :=
  ⟨-86672281/1000000000, 1024941/20000000⟩
def contact0030 : RatBall := localContactBall tau0030 center0030
def work0030 : RoundedTauEval :=
  evalTau precision tau0030 contact0030 logTwoBall

theorem center_sq0030 : (center0030.re : ℝ)^2 +
    (center0030.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0030]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0003


