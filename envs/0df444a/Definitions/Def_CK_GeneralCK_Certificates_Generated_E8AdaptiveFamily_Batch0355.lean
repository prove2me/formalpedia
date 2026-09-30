-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:51:17.872004+00:00
-- url     : https://prove2.me/theorems/d304c2e9-ca60-492d-b186-a23b14bd00f1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0355.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0355_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2845 : work2845.theta.ok = true ∧
    work2845.jac.invOK = true ∧ acceptsUnitSq work2845.out = true := by decide +kernel

def cell2845 : CellCertificate where
  tauBall := tau2845
  contactCenter := center2845
  contactBall := contact2845
  work := work2845
  center_sq := center_sq2845
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2845.1
  jac_ok := checks2845.2.1
  accepted := checks2845.2.2

def tau2846 : RatBall :=
  ⟨⟨-27/640, -49/128⟩, 3/1280⟩
def center2846 : GaussianRat :=
  ⟨-1076269/31250000, -69875701/250000000⟩
def contact2846 : RatBall := localContactBall tau2846 center2846
def work2846 : RoundedTauEval :=
  evalTau precision tau2846 contact2846 logTwoBall

theorem center_sq2846 : (center2846.re : ℝ)^2 +
    (center2846.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2846]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2846 : work2846.theta.ok = true ∧
    work2846.jac.invOK = true ∧ acceptsUnitSq work2846.out = true := by decide +kernel

def cell2846 : CellCertificate where
  tauBall := tau2846
  contactCenter := center2846
  contactBall := contact2846
  work := work2846
  center_sq := center_sq2846
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2846.1
  jac_ok := checks2846.2.1
  accepted := checks2846.2.2

def tau2847 : RatBall :=
  ⟨⟨-5/128, -49/128⟩, 3/1280⟩
def center2847 : GaussianRat :=
  ⟨-31895051/1000000000, -13979961/50000000⟩
def contact2847 : RatBall := localContactBall tau2847 center2847
def work2847 : RoundedTauEval :=
  evalTau precision tau2847 contact2847 logTwoBall

theorem center_sq2847 : (center2847.re : ℝ)^2 +
    (center2847.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2847]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2847 : work2847.theta.ok = true ∧
    work2847.jac.invOK = true ∧ acceptsUnitSq work2847.out = true := by decide +kernel

def cell2847 : CellCertificate where
  tauBall := tau2847
  contactCenter := center2847
  contactBall := contact2847
  work := work2847
  center_sq := center_sq2847
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2847.1
  jac_ok := checks2847.2.1
  accepted := checks2847.2.2

def cells : List CellCertificate := [cell2840, cell2841, cell2842, cell2843, cell2844, cell2845, cell2846, cell2847]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355


