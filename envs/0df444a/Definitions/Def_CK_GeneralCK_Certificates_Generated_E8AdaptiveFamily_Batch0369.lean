-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0369
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0369
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:48:24.52099+00:00
-- url     : https://prove2.me/theorems/50e0430b-1001-4153-983c-4bbfa228bd86
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0369.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2952 : RatBall :=
  ⟨⟨5/128, -247/640⟩, 3/1280⟩
def center2952 : GaussianRat :=
  ⟨7997111/250000000, -282149129/1000000000⟩
def contact2952 : RatBall := localContactBall tau2952 center2952
def work2952 : RoundedTauEval :=
  evalTau precision tau2952 contact2952 logTwoBall

theorem center_sq2952 : (center2952.re : ℝ)^2 +
    (center2952.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2952]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2952 : work2952.theta.ok = true ∧
    work2952.jac.invOK = true ∧ acceptsUnitSq work2952.out = true := by decide +kernel

def cell2952 : CellCertificate where
  tauBall := tau2952
  contactCenter := center2952
  contactBall := contact2952
  work := work2952
  center_sq := center_sq2952
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2952.1
  jac_ok := checks2952.2.1
  accepted := checks2952.2.2

def tau2953 : RatBall :=
  ⟨⟨27/640, -247/640⟩, 3/1280⟩
def center2953 : GaussianRat :=
  ⟨34541389/1000000000, -56410273/200000000⟩
def contact2953 : RatBall := localContactBall tau2953 center2953
def work2953 : RoundedTauEval :=
  evalTau precision tau2953 contact2953 logTwoBall

theorem center_sq2953 : (center2953.re : ℝ)^2 +
    (center2953.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2953]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2953 : work2953.theta.ok = true ∧
    work2953.jac.invOK = true ∧ acceptsUnitSq work2953.out = true := by decide +kernel

def cell2953 : CellCertificate where
  tauBall := tau2953
  contactCenter := center2953
  contactBall := contact2953
  work := work2953
  center_sq := center_sq2953
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2953.1
  jac_ok := checks2953.2.1
  accepted := checks2953.2.2

def tau2954 : RatBall :=
  ⟨⟨5/128, -49/128⟩, 3/1280⟩
def center2954 : GaussianRat :=
  ⟨31895051/1000000000, -13979961/50000000⟩
def contact2954 : RatBall := localContactBall tau2954 center2954
def work2954 : RoundedTauEval :=
  evalTau precision tau2954 contact2954 logTwoBall

theorem center_sq2954 : (center2954.re : ℝ)^2 +
    (center2954.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2954]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2954 : work2954.theta.ok = true ∧
    work2954.jac.invOK = true ∧ acceptsUnitSq work2954.out = true := by decide +kernel

def cell2954 : CellCertificate where
  tauBall := tau2954
  contactCenter := center2954
  contactBall := contact2954
  work := work2954
  center_sq := center_sq2954
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2954.1
  jac_ok := checks2954.2.1
  accepted := checks2954.2.2

def tau2955 : RatBall :=
  ⟨⟨27/640, -49/128⟩, 3/1280⟩
def center2955 : GaussianRat :=
  ⟨1076269/31250000, -69875701/250000000⟩
def contact2955 : RatBall := localContactBall tau2955 center2955
def work2955 : RoundedTauEval :=
  evalTau precision tau2955 contact2955 logTwoBall

theorem center_sq2955 : (center2955.re : ℝ)^2 +
    (center2955.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2955]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2955 : work2955.theta.ok = true ∧
    work2955.jac.invOK = true ∧ acceptsUnitSq work2955.out = true := by decide +kernel

def cell2955 : CellCertificate where
  tauBall := tau2955
  contactCenter := center2955
  contactBall := contact2955
  work := work2955
  center_sq := center_sq2955
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2955.1
  jac_ok := checks2955.2.1
  accepted := checks2955.2.2

def tau2956 : RatBall :=
  ⟨⟨29/640, -247/640⟩, 3/1280⟩
def center2956 : GaussianRat :=
  ⟨18546463/500000000, -281946171/1000000000⟩
def contact2956 : RatBall := localContactBall tau2956 center2956
def work2956 : RoundedTauEval :=
  evalTau precision tau2956 contact2956 logTwoBall

theorem center_sq2956 : (center2956.re : ℝ)^2 +
    (center2956.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2956]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2956 : work2956.theta.ok = true ∧
    work2956.jac.invOK = true ∧ acceptsUnitSq work2956.out = true := by decide +kernel

def cell2956 : CellCertificate where
  tauBall := tau2956
  contactCenter := center2956
  contactBall := contact2956
  work := work2956
  center_sq := center_sq2956
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2956.1
  jac_ok := checks2956.2.1
  accepted := checks2956.2.2

def tau2957 : RatBall :=
  ⟨⟨31/640, -247/640⟩, 3/1280⟩
def center2957 : GaussianRat :=
  ⟨4955369/125000000, -8807299/31250000⟩
def contact2957 : RatBall := localContactBall tau2957 center2957
def work2957 : RoundedTauEval :=
  evalTau precision tau2957 contact2957 logTwoBall

theorem center_sq2957 : (center2957.re : ℝ)^2 +
    (center2957.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2957]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2957 : work2957.theta.ok = true ∧
    work2957.jac.invOK = true ∧ acceptsUnitSq work2957.out = true := by decide +kernel

def cell2957 : CellCertificate where
  tauBall := tau2957
  contactCenter := center2957
  contactBall := contact2957
  work := work2957
  center_sq := center_sq2957
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2957.1
  jac_ok := checks2957.2.1
  accepted := checks2957.2.2

def tau2958 : RatBall :=
  ⟨⟨29/640, -49/128⟩, 3/1280⟩
def center2958 : GaussianRat :=
  ⟨4623097/125000000, -13969953/50000000⟩
def contact2958 : RatBall := localContactBall tau2958 center2958
def work2958 : RoundedTauEval :=
  evalTau precision tau2958 contact2958 logTwoBall

theorem center_sq2958 : (center2958.re : ℝ)^2 +
    (center2958.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2958]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2958 : work2958.theta.ok = true ∧
    work2958.jac.invOK = true ∧ acceptsUnitSq work2958.out = true := by decide +kernel

def cell2958 : CellCertificate where
  tauBall := tau2958
  contactCenter := center2958
  contactBall := contact2958
  work := work2958
  center_sq := center_sq2958
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2958.1
  jac_ok := checks2958.2.1
  accepted := checks2958.2.2

def tau2959 : RatBall :=
  ⟨⟨31/640, -49/128⟩, 3/1280⟩
def center2959 : GaussianRat :=
  ⟨19763727/500000000, -279288009/1000000000⟩
def contact2959 : RatBall := localContactBall tau2959 center2959
def work2959 : RoundedTauEval :=
  evalTau precision tau2959 contact2959 logTwoBall

theorem center_sq2959 : (center2959.re : ℝ)^2 +
    (center2959.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2959]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2959 : work2959.theta.ok = true ∧
    work2959.jac.invOK = true ∧ acceptsUnitSq work2959.out = true := by decide +kernel

def cell2959 : CellCertificate where
  tauBall := tau2959
  contactCenter := center2959
  contactBall := contact2959
  work := work2959
  center_sq := center_sq2959
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2959.1
  jac_ok := checks2959.2.1
  accepted := checks2959.2.2

def cells : List CellCertificate := [cell2952, cell2953, cell2954, cell2955, cell2956, cell2957, cell2958, cell2959]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369

end


