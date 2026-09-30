-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0004_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:00:00.87845+00:00
-- url     : https://prove2.me/theorems/547ae923-fd7a-41cc-8200-40e0c2d427a2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0004 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0032 : RatBall :=
  ⟨⟨-1/40, 1/40⟩, 3/80⟩
def center0032 : GaussianRat :=
  ⟨-17336181/1000000000, 17321167/1000000000⟩
def contact0032 : RatBall := localContactBall tau0032 center0032
def work0032 : RoundedTauEval :=
  evalTau precision tau0032 contact0032 logTwoBall

theorem center_sq0032 : (center0032.re : ℝ)^2 +
    (center0032.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0032]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0032 : work0032.theta.ok = true ∧
    work0032.jac.invOK = true ∧ acceptsUnitSq work0032.out = true := by decide +kernel

def cell0032 : CellCertificate where
  tauBall := tau0032
  contactCenter := center0032
  contactBall := contact0032
  work := work0032
  center_sq := center_sq0032
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0032.1
  jac_ok := checks0032.2.1
  accepted := checks0032.2.2

def tau0033 : RatBall :=
  ⟨⟨-3/40, 3/40⟩, 3/80⟩
def center0033 : GaussianRat :=
  ⟨-1304683/25000000, 51781961/1000000000⟩
def contact0033 : RatBall := localContactBall tau0033 center0033
def work0033 : RoundedTauEval :=
  evalTau precision tau0033 contact0033 logTwoBall

theorem center_sq0033 : (center0033.re : ℝ)^2 +
    (center0033.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0033]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0033 : work0033.theta.ok = true ∧
    work0033.jac.invOK = true ∧ acceptsUnitSq work0033.out = true := by decide +kernel

def cell0033 : CellCertificate where
  tauBall := tau0033
  contactCenter := center0033
  contactBall := contact0033
  work := work0033
  center_sq := center_sq0033
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0033.1
  jac_ok := checks0033.2.1
  accepted := checks0033.2.2

def tau0034 : RatBall :=
  ⟨⟨-1/40, 3/40⟩, 3/80⟩
def center0034 : GaussianRat :=
  ⟨-2178341/125000000, 3253349/62500000⟩
def contact0034 : RatBall := localContactBall tau0034 center0034
def work0034 : RoundedTauEval :=
  evalTau precision tau0034 contact0034 logTwoBall

theorem center_sq0034 : (center0034.re : ℝ)^2 +
    (center0034.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0034]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0034 : work0034.theta.ok = true ∧
    work0034.jac.invOK = true ∧ acceptsUnitSq work0034.out = true := by decide +kernel

def cell0034 : CellCertificate where
  tauBall := tau0034
  contactCenter := center0034
  contactBall := contact0034
  work := work0034
  center_sq := center_sq0034
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0034.1
  jac_ok := checks0034.2.1
  accepted := checks0034.2.2

def tau0035 : RatBall :=
  ⟨⟨-1/8, 1/8⟩, 3/80⟩
def center0035 : GaussianRat :=
  ⟨-87563403/1000000000, 85687457/1000000000⟩
def contact0035 : RatBall := localContactBall tau0035 center0035
def work0035 : RoundedTauEval :=
  evalTau precision tau0035 contact0035 logTwoBall

theorem center_sq0035 : (center0035.re : ℝ)^2 +
    (center0035.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0035]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0035 : work0035.theta.ok = true ∧
    work0035.jac.invOK = true ∧ acceptsUnitSq work0035.out = true := by decide +kernel

def cell0035 : CellCertificate where
  tauBall := tau0035
  contactCenter := center0035
  contactBall := contact0035
  work := work0035
  center_sq := center_sq0035
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0035.1
  jac_ok := checks0035.2.1
  accepted := checks0035.2.2

def tau0036 : RatBall :=
  ⟨⟨-3/40, 1/8⟩, 3/80⟩
def center0036 : GaussianRat :=
  ⟨-52733271/1000000000, 10824621/125000000⟩
def contact0036 : RatBall := localContactBall tau0036 center0036
def work0036 : RoundedTauEval :=
  evalTau precision tau0036 contact0036 logTwoBall

theorem center_sq0036 : (center0036.re : ℝ)^2 +
    (center0036.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0036]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0036 : work0036.theta.ok = true ∧
    work0036.jac.invOK = true ∧ acceptsUnitSq work0036.out = true := by decide +kernel

def cell0036 : CellCertificate where
  tauBall := tau0036
  contactCenter := center0036
  contactBall := contact0036
  work := work0036
  center_sq := center_sq0036
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0036.1
  jac_ok := checks0036.2.1
  accepted := checks0036.2.2

def tau0037 : RatBall :=
  ⟨⟨-1/40, 1/8⟩, 3/80⟩
def center0037 : GaussianRat :=
  ⟨-17610637/1000000000, 8705903/100000000⟩
def contact0037 : RatBall := localContactBall tau0037 center0037
def work0037 : RoundedTauEval :=
  evalTau precision tau0037 contact0037 logTwoBall

theorem center_sq0037 : (center0037.re : ℝ)^2 +
    (center0037.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0037]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0037 : work0037.theta.ok = true ∧
    work0037.jac.invOK = true ∧ acceptsUnitSq work0037.out = true := by decide +kernel

def cell0037 : CellCertificate where
  tauBall := tau0037
  contactCenter := center0037
  contactBall := contact0037
  work := work0037
  center_sq := center_sq0037
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0037.1
  jac_ok := checks0037.2.1
  accepted := checks0037.2.2

def tau0038 : RatBall :=
  ⟨⟨-1/40, 7/40⟩, 3/80⟩
def center0038 : GaussianRat :=
  ⟨-17893761/1000000000, 7658063/62500000⟩
def contact0038 : RatBall := localContactBall tau0038 center0038

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0004


