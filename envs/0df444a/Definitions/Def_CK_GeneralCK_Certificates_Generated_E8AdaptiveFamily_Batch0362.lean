-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0362
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0362
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:08:43.933982+00:00
-- url     : https://prove2.me/theorems/741f7dae-86ac-4e61-a030-d25dde8d065e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0362.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0362_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2902 : RatBall :=
  ⟨⟨9/640, -253/640⟩, 3/1280⟩
def center2902 : GaussianRat :=
  ⟨5815363/500000000, -145189259/500000000⟩
def contact2902 : RatBall := localContactBall tau2902 center2902
def work2902 : RoundedTauEval :=
  evalTau precision tau2902 contact2902 logTwoBall

theorem center_sq2902 : (center2902.re : ℝ)^2 +
    (center2902.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2902]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2902 : work2902.theta.ok = true ∧
    work2902.jac.invOK = true ∧ acceptsUnitSq work2902.out = true := by decide +kernel

def cell2902 : CellCertificate where
  tauBall := tau2902
  contactCenter := center2902
  contactBall := contact2902
  work := work2902
  center_sq := center_sq2902
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2902.1
  jac_ok := checks2902.2.1
  accepted := checks2902.2.2

def tau2903 : RatBall :=
  ⟨⟨11/640, -253/640⟩, 3/1280⟩
def center2903 : GaussianRat :=
  ⟨7107163/500000000, -290339131/1000000000⟩
def contact2903 : RatBall := localContactBall tau2903 center2903
def work2903 : RoundedTauEval :=
  evalTau precision tau2903 contact2903 logTwoBall

theorem center_sq2903 : (center2903.re : ℝ)^2 +
    (center2903.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2903]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2903 : work2903.theta.ok = true ∧
    work2903.jac.invOK = true ∧ acceptsUnitSq work2903.out = true := by decide +kernel

def cell2903 : CellCertificate where
  tauBall := tau2903
  contactCenter := center2903
  contactBall := contact2903
  work := work2903
  center_sq := center_sq2903
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2903.1
  jac_ok := checks2903.2.1
  accepted := checks2903.2.2

def cells : List CellCertificate := [cell2896, cell2897, cell2898, cell2899, cell2900, cell2901, cell2902, cell2903]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362


