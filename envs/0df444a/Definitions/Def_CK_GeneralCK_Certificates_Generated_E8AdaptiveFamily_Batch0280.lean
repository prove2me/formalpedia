-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0280
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0280
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:41:55.181849+00:00
-- url     : https://prove2.me/theorems/e0f2e241-a6c4-474b-ad57-cc3019e5eb2e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0280.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2240 : RatBall :=
  ⟨⟨1/320, 117/320⟩, 3/640⟩
def center2240 : GaussianRat :=
  ⟨314351/125000000, 66559541/250000000⟩
def contact2240 : RatBall := localContactBall tau2240 center2240
def work2240 : RoundedTauEval :=
  evalTau precision tau2240 contact2240 logTwoBall

theorem center_sq2240 : (center2240.re : ℝ)^2 +
    (center2240.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2240]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2240 : work2240.theta.ok = true ∧
    work2240.jac.invOK = true ∧ acceptsUnitSq work2240.out = true := by decide +kernel

def cell2240 : CellCertificate where
  tauBall := tau2240
  contactCenter := center2240
  contactBall := contact2240
  work := work2240
  center_sq := center_sq2240
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2240.1
  jac_ok := checks2240.2.1
  accepted := checks2240.2.2

def tau2241 : RatBall :=
  ⟨⟨3/320, 117/320⟩, 3/640⟩
def center2241 : GaussianRat :=
  ⟨7544037/1000000000, 16638159/62500000⟩
def contact2241 : RatBall := localContactBall tau2241 center2241
def work2241 : RoundedTauEval :=
  evalTau precision tau2241 contact2241 logTwoBall

theorem center_sq2241 : (center2241.re : ℝ)^2 +
    (center2241.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2241]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2241 : work2241.theta.ok = true ∧
    work2241.jac.invOK = true ∧ acceptsUnitSq work2241.out = true := by decide +kernel

def cell2241 : CellCertificate where
  tauBall := tau2241
  contactCenter := center2241
  contactBall := contact2241
  work := work2241
  center_sq := center_sq2241
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2241.1
  jac_ok := checks2241.2.1
  accepted := checks2241.2.2

def tau2242 : RatBall :=
  ⟨⟨1/320, 119/320⟩, 3/640⟩
def center2242 : GaussianRat :=
  ⟨1264407/500000000, 33910207/125000000⟩
def contact2242 : RatBall := localContactBall tau2242 center2242
def work2242 : RoundedTauEval :=
  evalTau precision tau2242 contact2242 logTwoBall

theorem center_sq2242 : (center2242.re : ℝ)^2 +
    (center2242.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2242]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2242 : work2242.theta.ok = true ∧
    work2242.jac.invOK = true ∧ acceptsUnitSq work2242.out = true := by decide +kernel

def cell2242 : CellCertificate where
  tauBall := tau2242
  contactCenter := center2242
  contactBall := contact2242
  work := work2242
  center_sq := center_sq2242
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2242.1
  jac_ok := checks2242.2.1
  accepted := checks2242.2.2

def tau2243 : RatBall :=
  ⟨⟨3/320, 119/320⟩, 3/640⟩
def center2243 : GaussianRat :=
  ⟨3793023/500000000, 135626627/500000000⟩
def contact2243 : RatBall := localContactBall tau2243 center2243
def work2243 : RoundedTauEval :=
  evalTau precision tau2243 contact2243 logTwoBall

theorem center_sq2243 : (center2243.re : ℝ)^2 +
    (center2243.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2243]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2243 : work2243.theta.ok = true ∧
    work2243.jac.invOK = true ∧ acceptsUnitSq work2243.out = true := by decide +kernel

def cell2243 : CellCertificate where
  tauBall := tau2243
  contactCenter := center2243
  contactBall := contact2243
  work := work2243
  center_sq := center_sq2243
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2243.1
  jac_ok := checks2243.2.1
  accepted := checks2243.2.2

def tau2244 : RatBall :=
  ⟨⟨1/64, 117/320⟩, 3/640⟩
def center2244 : GaussianRat :=
  ⟨1257211/100000000, 66538831/250000000⟩
def contact2244 : RatBall := localContactBall tau2244 center2244
def work2244 : RoundedTauEval :=
  evalTau precision tau2244 contact2244 logTwoBall

theorem center_sq2244 : (center2244.re : ℝ)^2 +
    (center2244.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2244]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2244 : work2244.theta.ok = true ∧
    work2244.jac.invOK = true ∧ acceptsUnitSq work2244.out = true := by decide +kernel

def cell2244 : CellCertificate where
  tauBall := tau2244
  contactCenter := center2244
  contactBall := contact2244
  work := work2244
  center_sq := center_sq2244
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2244.1
  jac_ok := checks2244.2.1
  accepted := checks2244.2.2

def tau2245 : RatBall :=
  ⟨⟨7/320, 117/320⟩, 3/640⟩
def center2245 : GaussianRat :=
  ⟨3519651/200000000, 8314767/31250000⟩
def contact2245 : RatBall := localContactBall tau2245 center2245
def work2245 : RoundedTauEval :=
  evalTau precision tau2245 contact2245 logTwoBall

theorem center_sq2245 : (center2245.re : ℝ)^2 +
    (center2245.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2245]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2245 : work2245.theta.ok = true ∧
    work2245.jac.invOK = true ∧ acceptsUnitSq work2245.out = true := by decide +kernel

def cell2245 : CellCertificate where
  tauBall := tau2245
  contactCenter := center2245
  contactBall := contact2245
  work := work2245
  center_sq := center_sq2245
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2245.1
  jac_ok := checks2245.2.1
  accepted := checks2245.2.2

def tau2246 : RatBall :=
  ⟨⟨1/64, 119/320⟩, 3/640⟩
def center2246 : GaussianRat :=
  ⟨1264209/100000000, 27119647/100000000⟩
def contact2246 : RatBall := localContactBall tau2246 center2246
def work2246 : RoundedTauEval :=
  evalTau precision tau2246 contact2246 logTwoBall

theorem center_sq2246 : (center2246.re : ℝ)^2 +
    (center2246.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2246]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2246 : work2246.theta.ok = true ∧
    work2246.jac.invOK = true ∧ acceptsUnitSq work2246.out = true := by decide +kernel

def cell2246 : CellCertificate where
  tauBall := tau2246
  contactCenter := center2246
  contactBall := contact2246
  work := work2246
  center_sq := center_sq2246
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2246.1
  jac_ok := checks2246.2.1
  accepted := checks2246.2.2

def tau2247 : RatBall :=
  ⟨⟨7/320, 119/320⟩, 3/640⟩
def center2247 : GaussianRat :=
  ⟨3539231/200000000, 67777837/250000000⟩
def contact2247 : RatBall := localContactBall tau2247 center2247
def work2247 : RoundedTauEval :=
  evalTau precision tau2247 contact2247 logTwoBall

theorem center_sq2247 : (center2247.re : ℝ)^2 +
    (center2247.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2247]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2247 : work2247.theta.ok = true ∧
    work2247.jac.invOK = true ∧ acceptsUnitSq work2247.out = true := by decide +kernel

def cell2247 : CellCertificate where
  tauBall := tau2247
  contactCenter := center2247
  contactBall := contact2247
  work := work2247
  center_sq := center_sq2247
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2247.1
  jac_ok := checks2247.2.1
  accepted := checks2247.2.2

def cells : List CellCertificate := [cell2240, cell2241, cell2242, cell2243, cell2244, cell2245, cell2246, cell2247]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280

end


