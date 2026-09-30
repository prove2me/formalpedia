-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:56.501386+00:00
-- url     : https://prove2.me/theorems/8d0f65b4-92de-41a8-a345-7c415a2c3802
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0008.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0008_part01

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0070 : RatBall :=
  ⟨⟨-3/80, -17/80⟩, 3/160⟩
def center0070 : GaussianRat :=
  ⟨-13627917/500000000, -149428611/1000000000⟩
def contact0070 : RatBall := localContactBall tau0070 center0070
def work0070 : RoundedTauEval :=
  evalTau precision tau0070 contact0070 logTwoBall

theorem center_sq0070 : (center0070.re : ℝ)^2 +
    (center0070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0070 : work0070.theta.ok = true ∧
    work0070.jac.invOK = true ∧ acceptsUnitSq work0070.out = true := by decide +kernel

def cell0070 : CellCertificate where
  tauBall := tau0070
  contactCenter := center0070
  contactBall := contact0070
  work := work0070
  center_sq := center_sq0070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0070.1
  jac_ok := checks0070.2.1
  accepted := checks0070.2.2

def tau0071 : RatBall :=
  ⟨⟨-1/80, -17/80⟩, 3/160⟩
def center0071 : GaussianRat :=
  ⟨-2272549/250000000, -14963863/100000000⟩
def contact0071 : RatBall := localContactBall tau0071 center0071
def work0071 : RoundedTauEval :=
  evalTau precision tau0071 contact0071 logTwoBall

theorem center_sq0071 : (center0071.re : ℝ)^2 +
    (center0071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0071 : work0071.theta.ok = true ∧
    work0071.jac.invOK = true ∧ acceptsUnitSq work0071.out = true := by decide +kernel

def cell0071 : CellCertificate where
  tauBall := tau0071
  contactCenter := center0071
  contactBall := contact0071
  work := work0071
  center_sq := center_sq0071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0071.1
  jac_ok := checks0071.2.1
  accepted := checks0071.2.2

def cells : List CellCertificate := [cell0064, cell0065, cell0066, cell0067, cell0068, cell0069, cell0070, cell0071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008


