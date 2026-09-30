-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:19:21.624159+00:00
-- url     : https://prove2.me/theorems/c4ba59e9-c571-48e0-8878-bae3fbf11b04
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0104.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0104_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0836 : work0836.theta.ok = true ∧
    work0836.jac.invOK = true ∧ acceptsUnitSq work0836.out = true := by decide +kernel

def cell0836 : CellCertificate where
  tauBall := tau0836
  contactCenter := center0836
  contactBall := contact0836
  work := work0836
  center_sq := center_sq0836
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0836.1
  jac_ok := checks0836.2.1
  accepted := checks0836.2.2

def tau0837 : RatBall :=
  ⟨⟨-47/160, 29/160⟩, 3/320⟩
def center0837 : GaussianRat :=
  ⟨-25481847/125000000, 58047077/500000000⟩
def contact0837 : RatBall := localContactBall tau0837 center0837
def work0837 : RoundedTauEval :=
  evalTau precision tau0837 contact0837 logTwoBall

theorem center_sq0837 : (center0837.re : ℝ)^2 +
    (center0837.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0837]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0837 : work0837.theta.ok = true ∧
    work0837.jac.invOK = true ∧ acceptsUnitSq work0837.out = true := by decide +kernel

def cell0837 : CellCertificate where
  tauBall := tau0837
  contactCenter := center0837
  contactBall := contact0837
  work := work0837
  center_sq := center_sq0837
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0837.1
  jac_ok := checks0837.2.1
  accepted := checks0837.2.2

def tau0838 : RatBall :=
  ⟨⟨-9/32, 29/160⟩, 3/320⟩
def center0838 : GaussianRat :=
  ⟨-97851331/500000000, 116935591/1000000000⟩
def contact0838 : RatBall := localContactBall tau0838 center0838
def work0838 : RoundedTauEval :=
  evalTau precision tau0838 contact0838 logTwoBall

theorem center_sq0838 : (center0838.re : ℝ)^2 +
    (center0838.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0838]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0838 : work0838.theta.ok = true ∧
    work0838.jac.invOK = true ∧ acceptsUnitSq work0838.out = true := by decide +kernel

def cell0838 : CellCertificate where
  tauBall := tau0838
  contactCenter := center0838
  contactBall := contact0838
  work := work0838
  center_sq := center_sq0838
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0838.1
  jac_ok := checks0838.2.1
  accepted := checks0838.2.2

def tau0839 : RatBall :=
  ⟨⟨-47/160, 31/160⟩, 3/320⟩
def center0839 : GaussianRat :=
  ⟨-40948189/200000000, 124226081/1000000000⟩
def contact0839 : RatBall := localContactBall tau0839 center0839
def work0839 : RoundedTauEval :=
  evalTau precision tau0839 contact0839 logTwoBall

theorem center_sq0839 : (center0839.re : ℝ)^2 +
    (center0839.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0839]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0839 : work0839.theta.ok = true ∧
    work0839.jac.invOK = true ∧ acceptsUnitSq work0839.out = true := by decide +kernel

def cell0839 : CellCertificate where
  tauBall := tau0839
  contactCenter := center0839
  contactBall := contact0839
  work := work0839
  center_sq := center_sq0839
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0839.1
  jac_ok := checks0839.2.1
  accepted := checks0839.2.2

def cells : List CellCertificate := [cell0832, cell0833, cell0834, cell0835, cell0836, cell0837, cell0838, cell0839]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104


