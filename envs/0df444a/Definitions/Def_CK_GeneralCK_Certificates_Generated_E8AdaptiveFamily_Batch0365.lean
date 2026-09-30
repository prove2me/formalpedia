-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0365
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0365
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:20:03.597494+00:00
-- url     : https://prove2.me/theorems/1c14f10b-0fd0-46bf-b7f4-31b418cdb4bf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0365.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0365_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def center2925 : GaussianRat :=
  ⟨12233721/500000000, -287526937/1000000000⟩
def contact2925 : RatBall := localContactBall tau2925 center2925
def work2925 : RoundedTauEval :=
  evalTau precision tau2925 contact2925 logTwoBall

theorem center_sq2925 : (center2925.re : ℝ)^2 +
    (center2925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2925 : work2925.theta.ok = true ∧
    work2925.jac.invOK = true ∧ acceptsUnitSq work2925.out = true := by decide +kernel

def cell2925 : CellCertificate where
  tauBall := tau2925
  contactCenter := center2925
  contactBall := contact2925
  work := work2925
  center_sq := center_sq2925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2925.1
  jac_ok := checks2925.2.1
  accepted := checks2925.2.2

def tau2926 : RatBall :=
  ⟨⟨17/640, -249/640⟩, 3/1280⟩
def center2926 : GaussianRat :=
  ⟨10914601/500000000, -285027327/1000000000⟩
def contact2926 : RatBall := localContactBall tau2926 center2926
def work2926 : RoundedTauEval :=
  evalTau precision tau2926 contact2926 logTwoBall

theorem center_sq2926 : (center2926.re : ℝ)^2 +
    (center2926.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2926]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2926 : work2926.theta.ok = true ∧
    work2926.jac.invOK = true ∧ acceptsUnitSq work2926.out = true := by decide +kernel

def cell2926 : CellCertificate where
  tauBall := tau2926
  contactCenter := center2926
  contactBall := contact2926
  work := work2926
  center_sq := center_sq2926
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2926.1
  jac_ok := checks2926.2.1
  accepted := checks2926.2.2

def tau2927 : RatBall :=
  ⟨⟨19/640, -249/640⟩, 3/1280⟩
def center2927 : GaussianRat :=
  ⟨6098577/250000000, -142479251/500000000⟩
def contact2927 : RatBall := localContactBall tau2927 center2927
def work2927 : RoundedTauEval :=
  evalTau precision tau2927 contact2927 logTwoBall

theorem center_sq2927 : (center2927.re : ℝ)^2 +
    (center2927.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2927]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2927 : work2927.theta.ok = true ∧
    work2927.jac.invOK = true ∧ acceptsUnitSq work2927.out = true := by decide +kernel

def cell2927 : CellCertificate where
  tauBall := tau2927
  contactCenter := center2927
  contactBall := contact2927
  work := work2927
  center_sq := center_sq2927
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2927.1
  jac_ok := checks2927.2.1
  accepted := checks2927.2.2

def cells : List CellCertificate := [cell2920, cell2921, cell2922, cell2923, cell2924, cell2925, cell2926, cell2927]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365


