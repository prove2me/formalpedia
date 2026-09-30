-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0288
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0288
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:05:53.950986+00:00
-- url     : https://prove2.me/theorems/0718bfea-ab8f-4b3b-bbdb-ac606d5e6a00
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0288.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2304 : RatBall :=
  ⟨⟨27/320, 119/320⟩, 3/640⟩
def center2304 : GaussianRat :=
  ⟨33978407/500000000, 67181393/250000000⟩
def contact2304 : RatBall := localContactBall tau2304 center2304
def work2304 : RoundedTauEval :=
  evalTau precision tau2304 contact2304 logTwoBall

theorem center_sq2304 : (center2304.re : ℝ)^2 +
    (center2304.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2304]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2304 : work2304.theta.ok = true ∧
    work2304.jac.invOK = true ∧ acceptsUnitSq work2304.out = true := by decide +kernel

def cell2304 : CellCertificate where
  tauBall := tau2304
  contactCenter := center2304
  contactBall := contact2304
  work := work2304
  center_sq := center_sq2304
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2304.1
  jac_ok := checks2304.2.1
  accepted := checks2304.2.2

def tau2305 : RatBall :=
  ⟨⟨29/320, 117/320⟩, 3/640⟩
def center2305 : GaussianRat :=
  ⟨7254231/100000000, 263374389/1000000000⟩
def contact2305 : RatBall := localContactBall tau2305 center2305
def work2305 : RoundedTauEval :=
  evalTau precision tau2305 contact2305 logTwoBall

theorem center_sq2305 : (center2305.re : ℝ)^2 +
    (center2305.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2305]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2305 : work2305.theta.ok = true ∧
    work2305.jac.invOK = true ∧ acceptsUnitSq work2305.out = true := by decide +kernel

def cell2305 : CellCertificate where
  tauBall := tau2305
  contactCenter := center2305
  contactBall := contact2305
  work := work2305
  center_sq := center_sq2305
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2305.1
  jac_ok := checks2305.2.1
  accepted := checks2305.2.2

def tau2306 : RatBall :=
  ⟨⟨31/320, 117/320⟩, 3/640⟩
def center2306 : GaussianRat :=
  ⟨774869/10000000, 65742793/250000000⟩
def contact2306 : RatBall := localContactBall tau2306 center2306
def work2306 : RoundedTauEval :=
  evalTau precision tau2306 contact2306 logTwoBall

theorem center_sq2306 : (center2306.re : ℝ)^2 +
    (center2306.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2306]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2306 : work2306.theta.ok = true ∧
    work2306.jac.invOK = true ∧ acceptsUnitSq work2306.out = true := by decide +kernel

def cell2306 : CellCertificate where
  tauBall := tau2306
  contactCenter := center2306
  contactBall := contact2306
  work := work2306
  center_sq := center_sq2306
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2306.1
  jac_ok := checks2306.2.1
  accepted := checks2306.2.2

def tau2307 : RatBall :=
  ⟨⟨29/320, 119/320⟩, 3/640⟩
def center2307 : GaussianRat :=
  ⟨14587643/200000000, 268337373/1000000000⟩
def contact2307 : RatBall := localContactBall tau2307 center2307
def work2307 : RoundedTauEval :=
  evalTau precision tau2307 contact2307 logTwoBall

theorem center_sq2307 : (center2307.re : ℝ)^2 +
    (center2307.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2307]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2307 : work2307.theta.ok = true ∧
    work2307.jac.invOK = true ∧ acceptsUnitSq work2307.out = true := by decide +kernel

def cell2307 : CellCertificate where
  tauBall := tau2307
  contactCenter := center2307
  contactBall := contact2307
  work := work2307
  center_sq := center_sq2307
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2307.1
  jac_ok := checks2307.2.1
  accepted := checks2307.2.2

def tau2308 : RatBall :=
  ⟨⟨31/320, 119/320⟩, 3/640⟩
def center2308 : GaussianRat :=
  ⟨77908577/1000000000, 267922911/1000000000⟩
def contact2308 : RatBall := localContactBall tau2308 center2308
def work2308 : RoundedTauEval :=
  evalTau precision tau2308 contact2308 logTwoBall

theorem center_sq2308 : (center2308.re : ℝ)^2 +
    (center2308.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2308]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2308 : work2308.theta.ok = true ∧
    work2308.jac.invOK = true ∧ acceptsUnitSq work2308.out = true := by decide +kernel

def cell2308 : CellCertificate where
  tauBall := tau2308
  contactCenter := center2308
  contactBall := contact2308
  work := work2308
  center_sq := center_sq2308
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2308.1
  jac_ok := checks2308.2.1
  accepted := checks2308.2.2

def tau2309 : RatBall :=
  ⟨⟨17/320, 121/320⟩, 3/640⟩
def center2309 : GaussianRat :=
  ⟨8630399/200000000, 275306779/1000000000⟩
def contact2309 : RatBall := localContactBall tau2309 center2309
def work2309 : RoundedTauEval :=
  evalTau precision tau2309 contact2309 logTwoBall

theorem center_sq2309 : (center2309.re : ℝ)^2 +
    (center2309.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2309]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2309 : work2309.theta.ok = true ∧
    work2309.jac.invOK = true ∧ acceptsUnitSq work2309.out = true := by decide +kernel

def cell2309 : CellCertificate where
  tauBall := tau2309
  contactCenter := center2309
  contactBall := contact2309
  work := work2309
  center_sq := center_sq2309
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2309.1
  jac_ok := checks2309.2.1
  accepted := checks2309.2.2

def tau2310 : RatBall :=
  ⟨⟨19/320, 121/320⟩, 3/640⟩
def center2310 : GaussianRat :=
  ⟨48205717/1000000000, 275046561/1000000000⟩
def contact2310 : RatBall := localContactBall tau2310 center2310
def work2310 : RoundedTauEval :=
  evalTau precision tau2310 contact2310 logTwoBall

theorem center_sq2310 : (center2310.re : ℝ)^2 +
    (center2310.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2310]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2310 : work2310.theta.ok = true ∧
    work2310.jac.invOK = true ∧ acceptsUnitSq work2310.out = true := by decide +kernel

def cell2310 : CellCertificate where
  tauBall := tau2310
  contactCenter := center2310
  contactBall := contact2310
  work := work2310
  center_sq := center_sq2310
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2310.1
  jac_ok := checks2310.2.1
  accepted := checks2310.2.2

def tau2311 : RatBall :=
  ⟨⟨21/320, 121/320⟩, 3/640⟩
def center2311 : GaussianRat :=
  ⟨53251841/1000000000, 54951623/200000000⟩
def contact2311 : RatBall := localContactBall tau2311 center2311
def work2311 : RoundedTauEval :=
  evalTau precision tau2311 contact2311 logTwoBall

theorem center_sq2311 : (center2311.re : ℝ)^2 +
    (center2311.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2311]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2311 : work2311.theta.ok = true ∧
    work2311.jac.invOK = true ∧ acceptsUnitSq work2311.out = true := by decide +kernel

def cell2311 : CellCertificate where
  tauBall := tau2311
  contactCenter := center2311
  contactBall := contact2311
  work := work2311
  center_sq := center_sq2311
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2311.1
  jac_ok := checks2311.2.1
  accepted := checks2311.2.2

def cells : List CellCertificate := [cell2304, cell2305, cell2306, cell2307, cell2308, cell2309, cell2310, cell2311]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288

end


