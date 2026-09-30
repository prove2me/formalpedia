-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0363
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0363
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:28:40.634792+00:00
-- url     : https://prove2.me/theorems/55b0a738-dcbd-4441-81d5-3c211eb7a161
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0363.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0363_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def contact2910 : RatBall := localContactBall tau2910 center2910
def work2910 : RoundedTauEval :=
  evalTau precision tau2910 contact2910 logTwoBall

theorem center_sq2910 : (center2910.re : ℝ)^2 +
    (center2910.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2910]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2910 : work2910.theta.ok = true ∧
    work2910.jac.invOK = true ∧ acceptsUnitSq work2910.out = true := by decide +kernel

def cell2910 : CellCertificate where
  tauBall := tau2910
  contactCenter := center2910
  contactBall := contact2910
  work := work2910
  center_sq := center_sq2910
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2910.1
  jac_ok := checks2910.2.1
  accepted := checks2910.2.2

def tau2911 : RatBall :=
  ⟨⟨11/640, -249/640⟩, 3/1280⟩
def center2911 : GaussianRat :=
  ⟨14128883/1000000000, -11407523/40000000⟩
def contact2911 : RatBall := localContactBall tau2911 center2911
def work2911 : RoundedTauEval :=
  evalTau precision tau2911 contact2911 logTwoBall

theorem center_sq2911 : (center2911.re : ℝ)^2 +
    (center2911.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2911]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2911 : work2911.theta.ok = true ∧
    work2911.jac.invOK = true ∧ acceptsUnitSq work2911.out = true := by decide +kernel

def cell2911 : CellCertificate where
  tauBall := tau2911
  contactCenter := center2911
  contactBall := contact2911
  work := work2911
  center_sq := center_sq2911
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2911.1
  jac_ok := checks2911.2.1
  accepted := checks2911.2.2

def cells : List CellCertificate := [cell2904, cell2905, cell2906, cell2907, cell2908, cell2909, cell2910, cell2911]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363


