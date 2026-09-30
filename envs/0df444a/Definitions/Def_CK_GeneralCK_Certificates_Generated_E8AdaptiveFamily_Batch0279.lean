-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0279
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0279
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:23:20.885442+00:00
-- url     : https://prove2.me/theorems/88d4379c-eff5-48d3-9c3a-490eea3701c5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0279.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2232 : RatBall :=
  ⟨⟨29/320, 109/320⟩, 3/640⟩
def center2232 : GaussianRat :=
  ⟨17765923/250000000, 243771477/1000000000⟩
def contact2232 : RatBall := localContactBall tau2232 center2232
def work2232 : RoundedTauEval :=
  evalTau precision tau2232 contact2232 logTwoBall

theorem center_sq2232 : (center2232.re : ℝ)^2 +
    (center2232.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2232]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2232 : work2232.theta.ok = true ∧
    work2232.jac.invOK = true ∧ acceptsUnitSq work2232.out = true := by decide +kernel

def cell2232 : CellCertificate where
  tauBall := tau2232
  contactCenter := center2232
  contactBall := contact2232
  work := work2232
  center_sq := center_sq2232
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2232.1
  jac_ok := checks2232.2.1
  accepted := checks2232.2.2

def tau2233 : RatBall :=
  ⟨⟨31/320, 109/320⟩, 3/640⟩
def center2233 : GaussianRat :=
  ⟨75911827/1000000000, 121705269/500000000⟩
def contact2233 : RatBall := localContactBall tau2233 center2233
def work2233 : RoundedTauEval :=
  evalTau precision tau2233 contact2233 logTwoBall

theorem center_sq2233 : (center2233.re : ℝ)^2 +
    (center2233.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2233]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2233 : work2233.theta.ok = true ∧
    work2233.jac.invOK = true ∧ acceptsUnitSq work2233.out = true := by decide +kernel

def cell2233 : CellCertificate where
  tauBall := tau2233
  contactCenter := center2233
  contactBall := contact2233
  work := work2233
  center_sq := center_sq2233
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2233.1
  jac_ok := checks2233.2.1
  accepted := checks2233.2.2

def tau2234 : RatBall :=
  ⟨⟨29/320, 111/320⟩, 3/640⟩
def center2234 : GaussianRat :=
  ⟨7141811/100000000, 9945447/40000000⟩
def contact2234 : RatBall := localContactBall tau2234 center2234
def work2234 : RoundedTauEval :=
  evalTau precision tau2234 contact2234 logTwoBall

theorem center_sq2234 : (center2234.re : ℝ)^2 +
    (center2234.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2234]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2234 : work2234.theta.ok = true ∧
    work2234.jac.invOK = true ∧ acceptsUnitSq work2234.out = true := by decide +kernel

def cell2234 : CellCertificate where
  tauBall := tau2234
  contactCenter := center2234
  contactBall := contact2234
  work := work2234
  center_sq := center_sq2234
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2234.1
  jac_ok := checks2234.2.1
  accepted := checks2234.2.2

def tau2235 : RatBall :=
  ⟨⟨31/320, 111/320⟩, 3/640⟩
def center2235 : GaussianRat :=
  ⟨76289393/1000000000, 248265049/1000000000⟩
def contact2235 : RatBall := localContactBall tau2235 center2235
def work2235 : RoundedTauEval :=
  evalTau precision tau2235 contact2235 logTwoBall

theorem center_sq2235 : (center2235.re : ℝ)^2 +
    (center2235.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2235]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2235 : work2235.theta.ok = true ∧
    work2235.jac.invOK = true ∧ acceptsUnitSq work2235.out = true := by decide +kernel

def cell2235 : CellCertificate where
  tauBall := tau2235
  contactCenter := center2235
  contactBall := contact2235
  work := work2235
  center_sq := center_sq2235
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2235.1
  jac_ok := checks2235.2.1
  accepted := checks2235.2.2

def tau2236 : RatBall :=
  ⟨⟨1/64, 113/320⟩, 3/640⟩
def center2236 : GaussianRat :=
  ⟨12437881/1000000000, 3201937/12500000⟩
def contact2236 : RatBall := localContactBall tau2236 center2236
def work2236 : RoundedTauEval :=
  evalTau precision tau2236 contact2236 logTwoBall

theorem center_sq2236 : (center2236.re : ℝ)^2 +
    (center2236.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2236]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2236 : work2236.theta.ok = true ∧
    work2236.jac.invOK = true ∧ acceptsUnitSq work2236.out = true := by decide +kernel

def cell2236 : CellCertificate where
  tauBall := tau2236
  contactCenter := center2236
  contactBall := contact2236
  work := work2236
  center_sq := center_sq2236
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2236.1
  jac_ok := checks2236.2.1
  accepted := checks2236.2.2

def tau2237 : RatBall :=
  ⟨⟨7/320, 113/320⟩, 3/640⟩
def center2237 : GaussianRat :=
  ⟨17410471/1000000000, 51215337/200000000⟩
def contact2237 : RatBall := localContactBall tau2237 center2237
def work2237 : RoundedTauEval :=
  evalTau precision tau2237 contact2237 logTwoBall

theorem center_sq2237 : (center2237.re : ℝ)^2 +
    (center2237.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2237]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2237 : work2237.theta.ok = true ∧
    work2237.jac.invOK = true ∧ acceptsUnitSq work2237.out = true := by decide +kernel

def cell2237 : CellCertificate where
  tauBall := tau2237
  contactCenter := center2237
  contactBall := contact2237
  work := work2237
  center_sq := center_sq2237
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2237.1
  jac_ok := checks2237.2.1
  accepted := checks2237.2.2

def tau2238 : RatBall :=
  ⟨⟨1/64, 23/64⟩, 3/640⟩
def center2238 : GaussianRat :=
  ⟨1563007/125000000, 13057087/50000000⟩
def contact2238 : RatBall := localContactBall tau2238 center2238
def work2238 : RoundedTauEval :=
  evalTau precision tau2238 contact2238 logTwoBall

theorem center_sq2238 : (center2238.re : ℝ)^2 +
    (center2238.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2238]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2238 : work2238.theta.ok = true ∧
    work2238.jac.invOK = true ∧ acceptsUnitSq work2238.out = true := by decide +kernel

def cell2238 : CellCertificate where
  tauBall := tau2238
  contactCenter := center2238
  contactBall := contact2238
  work := work2238
  center_sq := center_sq2238
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2238.1
  jac_ok := checks2238.2.1
  accepted := checks2238.2.2

def tau2239 : RatBall :=
  ⟨⟨7/320, 23/64⟩, 3/640⟩
def center2239 : GaussianRat :=
  ⟨350061/20000000, 130530621/500000000⟩
def contact2239 : RatBall := localContactBall tau2239 center2239
def work2239 : RoundedTauEval :=
  evalTau precision tau2239 contact2239 logTwoBall

theorem center_sq2239 : (center2239.re : ℝ)^2 +
    (center2239.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2239]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2239 : work2239.theta.ok = true ∧
    work2239.jac.invOK = true ∧ acceptsUnitSq work2239.out = true := by decide +kernel

def cell2239 : CellCertificate where
  tauBall := tau2239
  contactCenter := center2239
  contactBall := contact2239
  work := work2239
  center_sq := center_sq2239
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2239.1
  jac_ok := checks2239.2.1
  accepted := checks2239.2.2

def cells : List CellCertificate := [cell2232, cell2233, cell2234, cell2235, cell2236, cell2237, cell2238, cell2239]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279

end


