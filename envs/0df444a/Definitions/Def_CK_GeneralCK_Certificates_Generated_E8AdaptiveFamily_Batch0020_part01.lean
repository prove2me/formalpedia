-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:24:27.340752+00:00
-- url     : https://prove2.me/theorems/aec85358-0f16-4e12-965d-633a496a8679
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0020 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0020_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0162 : work0162.theta.ok = true ∧
    work0162.jac.invOK = true ∧ acceptsUnitSq work0162.out = true := by decide +kernel

def cell0162 : CellCertificate where
  tauBall := tau0162
  contactCenter := center0162
  contactBall := contact0162
  work := work0162
  center_sq := center_sq0162
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0162.1
  jac_ok := checks0162.2.1
  accepted := checks0162.2.2

def tau0163 : RatBall :=
  ⟨⟨19/80, -13/80⟩, 3/160⟩
def center0163 : GaussianRat :=
  ⟨41411389/250000000, -107116873/1000000000⟩
def contact0163 : RatBall := localContactBall tau0163 center0163
def work0163 : RoundedTauEval :=
  evalTau precision tau0163 contact0163 logTwoBall

theorem center_sq0163 : (center0163.re : ℝ)^2 +
    (center0163.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0163]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0163 : work0163.theta.ok = true ∧
    work0163.jac.invOK = true ∧ acceptsUnitSq work0163.out = true := by decide +kernel

def cell0163 : CellCertificate where
  tauBall := tau0163
  contactCenter := center0163
  contactBall := contact0163
  work := work0163
  center_sq := center_sq0163
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0163.1
  jac_ok := checks0163.2.1
  accepted := checks0163.2.2

def tau0164 : RatBall :=
  ⟨⟨21/80, -13/80⟩, 3/160⟩
def center0164 : GaussianRat :=
  ⟨4555953/25000000, -105764329/1000000000⟩
def contact0164 : RatBall := localContactBall tau0164 center0164
def work0164 : RoundedTauEval :=
  evalTau precision tau0164 contact0164 logTwoBall

theorem center_sq0164 : (center0164.re : ℝ)^2 +
    (center0164.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0164]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0164 : work0164.theta.ok = true ∧
    work0164.jac.invOK = true ∧ acceptsUnitSq work0164.out = true := by decide +kernel

def cell0164 : CellCertificate where
  tauBall := tau0164
  contactCenter := center0164
  contactBall := contact0164
  work := work0164
  center_sq := center_sq0164
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0164.1
  jac_ok := checks0164.2.1
  accepted := checks0164.2.2

def tau0165 : RatBall :=
  ⟨⟨17/80, -11/80⟩, 3/160⟩
def center0165 : GaussianRat :=
  ⟨1154229/7812500, -91503559/1000000000⟩
def contact0165 : RatBall := localContactBall tau0165 center0165

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020


