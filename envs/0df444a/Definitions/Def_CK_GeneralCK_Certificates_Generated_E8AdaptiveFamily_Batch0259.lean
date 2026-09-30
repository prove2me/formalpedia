-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0259
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0259
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:37:38.009477+00:00
-- url     : https://prove2.me/theorems/b17b5722-5b7b-45cd-9943-40105b215f16
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0259.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2072 : RatBall :=
  ⟨⟨-49/320, 107/320⟩, 3/640⟩
def center2072 : GaussianRat :=
  ⟨-5922481/50000000, 234456553/1000000000⟩
def contact2072 : RatBall := localContactBall tau2072 center2072
def work2072 : RoundedTauEval :=
  evalTau precision tau2072 contact2072 logTwoBall

theorem center_sq2072 : (center2072.re : ℝ)^2 +
    (center2072.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2072]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2072 : work2072.theta.ok = true ∧
    work2072.jac.invOK = true ∧ acceptsUnitSq work2072.out = true := by decide +kernel

def cell2072 : CellCertificate where
  tauBall := tau2072
  contactCenter := center2072
  contactBall := contact2072
  work := work2072
  center_sq := center_sq2072
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2072.1
  jac_ok := checks2072.2.1
  accepted := checks2072.2.2

def tau2073 : RatBall :=
  ⟨⟨-11/64, 109/320⟩, 3/640⟩
def center2073 : GaussianRat :=
  ⟨-133113831/1000000000, 118694053/500000000⟩
def contact2073 : RatBall := localContactBall tau2073 center2073
def work2073 : RoundedTauEval :=
  evalTau precision tau2073 contact2073 logTwoBall

theorem center_sq2073 : (center2073.re : ℝ)^2 +
    (center2073.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2073]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2073 : work2073.theta.ok = true ∧
    work2073.jac.invOK = true ∧ acceptsUnitSq work2073.out = true := by decide +kernel

def cell2073 : CellCertificate where
  tauBall := tau2073
  contactCenter := center2073
  contactBall := contact2073
  work := work2073
  center_sq := center_sq2073
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2073.1
  jac_ok := checks2073.2.1
  accepted := checks2073.2.2

def tau2074 : RatBall :=
  ⟨⟨-53/320, 109/320⟩, 3/640⟩
def center2074 : GaussianRat :=
  ⟨-25685587/200000000, 238002417/1000000000⟩
def contact2074 : RatBall := localContactBall tau2074 center2074
def work2074 : RoundedTauEval :=
  evalTau precision tau2074 contact2074 logTwoBall

theorem center_sq2074 : (center2074.re : ℝ)^2 +
    (center2074.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2074]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2074 : work2074.theta.ok = true ∧
    work2074.jac.invOK = true ∧ acceptsUnitSq work2074.out = true := by decide +kernel

def cell2074 : CellCertificate where
  tauBall := tau2074
  contactCenter := center2074
  contactBall := contact2074
  work := work2074
  center_sq := center_sq2074
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2074.1
  jac_ok := checks2074.2.1
  accepted := checks2074.2.2

def tau2075 : RatBall :=
  ⟨⟨-11/64, 111/320⟩, 3/640⟩
def center2075 : GaussianRat :=
  ⟨-133746201/1000000000, 121037589/500000000⟩
def contact2075 : RatBall := localContactBall tau2075 center2075
def work2075 : RoundedTauEval :=
  evalTau precision tau2075 contact2075 logTwoBall

theorem center_sq2075 : (center2075.re : ℝ)^2 +
    (center2075.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2075]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2075 : work2075.theta.ok = true ∧
    work2075.jac.invOK = true ∧ acceptsUnitSq work2075.out = true := by decide +kernel

def cell2075 : CellCertificate where
  tauBall := tau2075
  contactCenter := center2075
  contactBall := contact2075
  work := work2075
  center_sq := center_sq2075
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2075.1
  jac_ok := checks2075.2.1
  accepted := checks2075.2.2

def tau2076 : RatBall :=
  ⟨⟨-53/320, 111/320⟩, 3/640⟩
def center2076 : GaussianRat :=
  ⟨-4032529/31250000, 121353177/500000000⟩
def contact2076 : RatBall := localContactBall tau2076 center2076
def work2076 : RoundedTauEval :=
  evalTau precision tau2076 contact2076 logTwoBall

theorem center_sq2076 : (center2076.re : ℝ)^2 +
    (center2076.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2076]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2076 : work2076.theta.ok = true ∧
    work2076.jac.invOK = true ∧ acceptsUnitSq work2076.out = true := by decide +kernel

def cell2076 : CellCertificate where
  tauBall := tau2076
  contactCenter := center2076
  contactBall := contact2076
  work := work2076
  center_sq := center_sq2076
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2076.1
  jac_ok := checks2076.2.1
  accepted := checks2076.2.2

def tau2077 : RatBall :=
  ⟨⟨-51/320, 109/320⟩, 3/640⟩
def center2077 : GaussianRat :=
  ⟨-61862799/500000000, 238597409/1000000000⟩
def contact2077 : RatBall := localContactBall tau2077 center2077
def work2077 : RoundedTauEval :=
  evalTau precision tau2077 contact2077 logTwoBall

theorem center_sq2077 : (center2077.re : ℝ)^2 +
    (center2077.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2077]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2077 : work2077.theta.ok = true ∧
    work2077.jac.invOK = true ∧ acceptsUnitSq work2077.out = true := by decide +kernel

def cell2077 : CellCertificate where
  tauBall := tau2077
  contactCenter := center2077
  contactBall := contact2077
  work := work2077
  center_sq := center_sq2077
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2077.1
  jac_ok := checks2077.2.1
  accepted := checks2077.2.2

def tau2078 : RatBall :=
  ⟨⟨-49/320, 109/320⟩, 3/640⟩
def center2078 : GaussianRat :=
  ⟨-119007309/1000000000, 59793181/250000000⟩
def contact2078 : RatBall := localContactBall tau2078 center2078
def work2078 : RoundedTauEval :=
  evalTau precision tau2078 contact2078 logTwoBall

theorem center_sq2078 : (center2078.re : ℝ)^2 +
    (center2078.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2078]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2078 : work2078.theta.ok = true ∧
    work2078.jac.invOK = true ∧ acceptsUnitSq work2078.out = true := by decide +kernel

def cell2078 : CellCertificate where
  tauBall := tau2078
  contactCenter := center2078
  contactBall := contact2078
  work := work2078
  center_sq := center_sq2078
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2078.1
  jac_ok := checks2078.2.1
  accepted := checks2078.2.2

def tau2079 : RatBall :=
  ⟨⟨-51/320, 111/320⟩, 3/640⟩
def center2079 : GaussianRat :=
  ⟨-124318847/1000000000, 121658863/500000000⟩
def contact2079 : RatBall := localContactBall tau2079 center2079
def work2079 : RoundedTauEval :=
  evalTau precision tau2079 contact2079 logTwoBall

theorem center_sq2079 : (center2079.re : ℝ)^2 +
    (center2079.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2079]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2079 : work2079.theta.ok = true ∧
    work2079.jac.invOK = true ∧ acceptsUnitSq work2079.out = true := by decide +kernel

def cell2079 : CellCertificate where
  tauBall := tau2079
  contactCenter := center2079
  contactBall := contact2079
  work := work2079
  center_sq := center_sq2079
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2079.1
  jac_ok := checks2079.2.1
  accepted := checks2079.2.2

def cells : List CellCertificate := [cell2072, cell2073, cell2074, cell2075, cell2076, cell2077, cell2078, cell2079]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259

end


