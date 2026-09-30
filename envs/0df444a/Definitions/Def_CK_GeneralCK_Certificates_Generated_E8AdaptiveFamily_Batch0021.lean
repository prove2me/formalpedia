-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:45:41.119079+00:00
-- url     : https://prove2.me/theorems/76437e17-bb89-4c72-a3d6-844e07fa9e7f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0021.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0021_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0172 : work0172.theta.ok = true ∧
    work0172.jac.invOK = true ∧ acceptsUnitSq work0172.out = true := by decide +kernel

def cell0172 : CellCertificate where
  tauBall := tau0172
  contactCenter := center0172
  contactBall := contact0172
  work := work0172
  center_sq := center_sq0172
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0172.1
  jac_ok := checks0172.2.1
  accepted := checks0172.2.2

def tau0173 : RatBall :=
  ⟨⟨5/16, -9/80⟩, 3/160⟩
def center0173 : GaussianRat :=
  ⟨106033397/500000000, -70959907/1000000000⟩
def contact0173 : RatBall := localContactBall tau0173 center0173
def work0173 : RoundedTauEval :=
  evalTau precision tau0173 contact0173 logTwoBall

theorem center_sq0173 : (center0173.re : ℝ)^2 +
    (center0173.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0173]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0173 : work0173.theta.ok = true ∧
    work0173.jac.invOK = true ∧ acceptsUnitSq work0173.out = true := by decide +kernel

def cell0173 : CellCertificate where
  tauBall := tau0173
  contactCenter := center0173
  contactBall := contact0173
  work := work0173
  center_sq := center_sq0173
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0173.1
  jac_ok := checks0173.2.1
  accepted := checks0173.2.2

def tau0174 : RatBall :=
  ⟨⟨17/80, -7/80⟩, 3/160⟩
def center0174 : GaussianRat :=
  ⟨146129149/1000000000, -3628117/62500000⟩
def contact0174 : RatBall := localContactBall tau0174 center0174
def work0174 : RoundedTauEval :=
  evalTau precision tau0174 contact0174 logTwoBall

theorem center_sq0174 : (center0174.re : ℝ)^2 +
    (center0174.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0174]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0174 : work0174.theta.ok = true ∧
    work0174.jac.invOK = true ∧ acceptsUnitSq work0174.out = true := by decide +kernel

def cell0174 : CellCertificate where
  tauBall := tau0174
  contactCenter := center0174
  contactBall := contact0174
  work := work0174
  center_sq := center_sq0174
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0174.1
  jac_ok := checks0174.2.1
  accepted := checks0174.2.2

def tau0175 : RatBall :=
  ⟨⟨19/80, -7/80⟩, 3/160⟩
def center0175 : GaussianRat :=
  ⟨162690477/1000000000, -28700003/500000000⟩
def contact0175 : RatBall := localContactBall tau0175 center0175
def work0175 : RoundedTauEval :=
  evalTau precision tau0175 contact0175 logTwoBall

theorem center_sq0175 : (center0175.re : ℝ)^2 +
    (center0175.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0175]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0175 : work0175.theta.ok = true ∧
    work0175.jac.invOK = true ∧ acceptsUnitSq work0175.out = true := by decide +kernel

def cell0175 : CellCertificate where
  tauBall := tau0175
  contactCenter := center0175
  contactBall := contact0175
  work := work0175
  center_sq := center_sq0175
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0175.1
  jac_ok := checks0175.2.1
  accepted := checks0175.2.2

def cells : List CellCertificate := [cell0168, cell0169, cell0170, cell0171, cell0172, cell0173, cell0174, cell0175]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021


