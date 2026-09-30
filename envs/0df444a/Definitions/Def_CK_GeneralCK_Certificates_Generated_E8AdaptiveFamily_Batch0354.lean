-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:34:32.094529+00:00
-- url     : https://prove2.me/theorems/d730091f-9155-4fbb-9006-a0e7dcedf971
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0354.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0354_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2837 : (center2837.re : ℝ)^2 +
    (center2837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2837 : work2837.theta.ok = true ∧
    work2837.jac.invOK = true ∧ acceptsUnitSq work2837.out = true := by decide +kernel

def cell2837 : CellCertificate where
  tauBall := tau2837
  contactCenter := center2837
  contactBall := contact2837
  work := work2837
  center_sq := center_sq2837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2837.1
  jac_ok := checks2837.2.1
  accepted := checks2837.2.2

def tau2838 : RatBall :=
  ⟨⟨-19/640, -249/640⟩, 3/1280⟩
def center2838 : GaussianRat :=
  ⟨-6098577/250000000, -142479251/500000000⟩
def contact2838 : RatBall := localContactBall tau2838 center2838
def work2838 : RoundedTauEval :=
  evalTau precision tau2838 contact2838 logTwoBall

theorem center_sq2838 : (center2838.re : ℝ)^2 +
    (center2838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2838 : work2838.theta.ok = true ∧
    work2838.jac.invOK = true ∧ acceptsUnitSq work2838.out = true := by decide +kernel

def cell2838 : CellCertificate where
  tauBall := tau2838
  contactCenter := center2838
  contactBall := contact2838
  work := work2838
  center_sq := center_sq2838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2838.1
  jac_ok := checks2838.2.1
  accepted := checks2838.2.2

def tau2839 : RatBall :=
  ⟨⟨-17/640, -249/640⟩, 3/1280⟩
def center2839 : GaussianRat :=
  ⟨-10914601/500000000, -285027327/1000000000⟩
def contact2839 : RatBall := localContactBall tau2839 center2839
def work2839 : RoundedTauEval :=
  evalTau precision tau2839 contact2839 logTwoBall

theorem center_sq2839 : (center2839.re : ℝ)^2 +
    (center2839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2839 : work2839.theta.ok = true ∧
    work2839.jac.invOK = true ∧ acceptsUnitSq work2839.out = true := by decide +kernel

def cell2839 : CellCertificate where
  tauBall := tau2839
  contactCenter := center2839
  contactBall := contact2839
  work := work2839
  center_sq := center_sq2839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2839.1
  jac_ok := checks2839.2.1
  accepted := checks2839.2.2

def cells : List CellCertificate := [cell2832, cell2833, cell2834, cell2835, cell2836, cell2837, cell2838, cell2839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354


