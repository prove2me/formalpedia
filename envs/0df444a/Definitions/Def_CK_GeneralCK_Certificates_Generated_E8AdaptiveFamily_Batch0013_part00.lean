-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0013_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0013_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:43:18.198133+00:00
-- url     : https://prove2.me/theorems/ddd085b8-e14e-40a2-b4fa-9d09ad4b3fe4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0013 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0104 : RatBall :=
  ⟨⟨-17/80, -1/16⟩, 3/160⟩
def center0104 : GaussianRat :=
  ⟨-29119789/200000000, -10355411/250000000⟩
def contact0104 : RatBall := localContactBall tau0104 center0104
def work0104 : RoundedTauEval :=
  evalTau precision tau0104 contact0104 logTwoBall

theorem center_sq0104 : (center0104.re : ℝ)^2 +
    (center0104.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0104]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0104 : work0104.theta.ok = true ∧
    work0104.jac.invOK = true ∧ acceptsUnitSq work0104.out = true := by decide +kernel

def cell0104 : CellCertificate where
  tauBall := tau0104
  contactCenter := center0104
  contactBall := contact0104
  work := work0104
  center_sq := center_sq0104
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0104.1
  jac_ok := checks0104.2.1
  accepted := checks0104.2.2

def tau0105 : RatBall :=
  ⟨⟨-23/80, -3/80⟩, 3/160⟩
def center0105 : GaussianRat :=
  ⟨-4852301/25000000, -23940531/1000000000⟩
def contact0105 : RatBall := localContactBall tau0105 center0105
def work0105 : RoundedTauEval :=
  evalTau precision tau0105 contact0105 logTwoBall

theorem center_sq0105 : (center0105.re : ℝ)^2 +
    (center0105.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0105]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0105 : work0105.theta.ok = true ∧
    work0105.jac.invOK = true ∧ acceptsUnitSq work0105.out = true := by decide +kernel

def cell0105 : CellCertificate where
  tauBall := tau0105
  contactCenter := center0105
  contactBall := contact0105
  work := work0105
  center_sq := center_sq0105
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0105.1
  jac_ok := checks0105.2.1
  accepted := checks0105.2.2

def tau0106 : RatBall :=
  ⟨⟨-21/80, -3/80⟩, 3/160⟩
def center0106 : GaussianRat :=
  ⟨-89006593/500000000, -4852281/200000000⟩
def contact0106 : RatBall := localContactBall tau0106 center0106
def work0106 : RoundedTauEval :=
  evalTau precision tau0106 contact0106 logTwoBall

theorem center_sq0106 : (center0106.re : ℝ)^2 +
    (center0106.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0106]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0106 : work0106.theta.ok = true ∧
    work0106.jac.invOK = true ∧ acceptsUnitSq work0106.out = true := by decide +kernel

def cell0106 : CellCertificate where
  tauBall := tau0106
  contactCenter := center0106
  contactBall := contact0106
  work := work0106
  center_sq := center_sq0106
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0106.1
  jac_ok := checks0106.2.1
  accepted := checks0106.2.2

def tau0107 : RatBall :=
  ⟨⟨-23/80, -1/80⟩, 3/160⟩
def center0107 : GaussianRat :=
  ⟨-7754861/40000000, -3988989/500000000⟩
def contact0107 : RatBall := localContactBall tau0107 center0107
def work0107 : RoundedTauEval :=
  evalTau precision tau0107 contact0107 logTwoBall

theorem center_sq0107 : (center0107.re : ℝ)^2 +
    (center0107.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0107]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0107 : work0107.theta.ok = true ∧
    work0107.jac.invOK = true ∧ acceptsUnitSq work0107.out = true := by decide +kernel

def cell0107 : CellCertificate where
  tauBall := tau0107
  contactCenter := center0107
  contactBall := contact0107
  work := work0107
  center_sq := center_sq0107
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0107.1
  jac_ok := checks0107.2.1
  accepted := checks0107.2.2

def tau0108 : RatBall :=
  ⟨⟨-21/80, -1/80⟩, 3/160⟩
def center0108 : GaussianRat :=
  ⟨-4445163/25000000, -8084719/1000000000⟩
def contact0108 : RatBall := localContactBall tau0108 center0108
def work0108 : RoundedTauEval :=
  evalTau precision tau0108 contact0108 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013


