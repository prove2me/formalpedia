-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0267
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0267
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:53:25.362609+00:00
-- url     : https://prove2.me/theorems/a079b501-14fd-4f53-8f4a-e301ca0cfcad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0267.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2136 : RatBall :=
  ⟨⟨-29/320, 109/320⟩, 3/640⟩
def center2136 : GaussianRat :=
  ⟨-17765923/250000000, 243771477/1000000000⟩
def contact2136 : RatBall := localContactBall tau2136 center2136
def work2136 : RoundedTauEval :=
  evalTau precision tau2136 contact2136 logTwoBall

theorem center_sq2136 : (center2136.re : ℝ)^2 +
    (center2136.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2136]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2136 : work2136.theta.ok = true ∧
    work2136.jac.invOK = true ∧ acceptsUnitSq work2136.out = true := by decide +kernel

def cell2136 : CellCertificate where
  tauBall := tau2136
  contactCenter := center2136
  contactBall := contact2136
  work := work2136
  center_sq := center_sq2136
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2136.1
  jac_ok := checks2136.2.1
  accepted := checks2136.2.2

def tau2137 : RatBall :=
  ⟨⟨-31/320, 111/320⟩, 3/640⟩
def center2137 : GaussianRat :=
  ⟨-76289393/1000000000, 248265049/1000000000⟩
def contact2137 : RatBall := localContactBall tau2137 center2137
def work2137 : RoundedTauEval :=
  evalTau precision tau2137 contact2137 logTwoBall

theorem center_sq2137 : (center2137.re : ℝ)^2 +
    (center2137.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2137]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2137 : work2137.theta.ok = true ∧
    work2137.jac.invOK = true ∧ acceptsUnitSq work2137.out = true := by decide +kernel

def cell2137 : CellCertificate where
  tauBall := tau2137
  contactCenter := center2137
  contactBall := contact2137
  work := work2137
  center_sq := center_sq2137
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2137.1
  jac_ok := checks2137.2.1
  accepted := checks2137.2.2

def tau2138 : RatBall :=
  ⟨⟨-29/320, 111/320⟩, 3/640⟩
def center2138 : GaussianRat :=
  ⟨-7141811/100000000, 9945447/40000000⟩
def contact2138 : RatBall := localContactBall tau2138 center2138
def work2138 : RoundedTauEval :=
  evalTau precision tau2138 contact2138 logTwoBall

theorem center_sq2138 : (center2138.re : ℝ)^2 +
    (center2138.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2138]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2138 : work2138.theta.ok = true ∧
    work2138.jac.invOK = true ∧ acceptsUnitSq work2138.out = true := by decide +kernel

def cell2138 : CellCertificate where
  tauBall := tau2138
  contactCenter := center2138
  contactBall := contact2138
  work := work2138
  center_sq := center_sq2138
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2138.1
  jac_ok := checks2138.2.1
  accepted := checks2138.2.2

def tau2139 : RatBall :=
  ⟨⟨-27/320, 109/320⟩, 3/640⟩
def center2139 : GaussianRat :=
  ⟨-16551451/250000000, 30513683/125000000⟩
def contact2139 : RatBall := localContactBall tau2139 center2139
def work2139 : RoundedTauEval :=
  evalTau precision tau2139 contact2139 logTwoBall

theorem center_sq2139 : (center2139.re : ℝ)^2 +
    (center2139.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2139]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2139 : work2139.theta.ok = true ∧
    work2139.jac.invOK = true ∧ acceptsUnitSq work2139.out = true := by decide +kernel

def cell2139 : CellCertificate where
  tauBall := tau2139
  contactCenter := center2139
  contactBall := contact2139
  work := work2139
  center_sq := center_sq2139
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2139.1
  jac_ok := checks2139.2.1
  accepted := checks2139.2.2

def tau2140 : RatBall :=
  ⟨⟨-5/64, 109/320⟩, 3/640⟩
def center2140 : GaussianRat :=
  ⟨-6133879/100000000, 244424273/1000000000⟩
def contact2140 : RatBall := localContactBall tau2140 center2140
def work2140 : RoundedTauEval :=
  evalTau precision tau2140 contact2140 logTwoBall

theorem center_sq2140 : (center2140.re : ℝ)^2 +
    (center2140.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2140]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2140 : work2140.theta.ok = true ∧
    work2140.jac.invOK = true ∧ acceptsUnitSq work2140.out = true := by decide +kernel

def cell2140 : CellCertificate where
  tauBall := tau2140
  contactCenter := center2140
  contactBall := contact2140
  work := work2140
  center_sq := center_sq2140
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2140.1
  jac_ok := checks2140.2.1
  accepted := checks2140.2.2

def tau2141 : RatBall :=
  ⟨⟨-27/320, 111/320⟩, 3/640⟩
def center2141 : GaussianRat :=
  ⟨-66536837/1000000000, 62245929/250000000⟩
def contact2141 : RatBall := localContactBall tau2141 center2141
def work2141 : RoundedTauEval :=
  evalTau precision tau2141 contact2141 logTwoBall

theorem center_sq2141 : (center2141.re : ℝ)^2 +
    (center2141.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2141]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2141 : work2141.theta.ok = true ∧
    work2141.jac.invOK = true ∧ acceptsUnitSq work2141.out = true := by decide +kernel

def cell2141 : CellCertificate where
  tauBall := tau2141
  contactCenter := center2141
  contactBall := contact2141
  work := work2141
  center_sq := center_sq2141
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2141.1
  jac_ok := checks2141.2.1
  accepted := checks2141.2.2

def tau2142 : RatBall :=
  ⟨⟨-5/64, 111/320⟩, 3/640⟩
def center2142 : GaussianRat :=
  ⟨-30823109/500000000, 249307439/1000000000⟩
def contact2142 : RatBall := localContactBall tau2142 center2142
def work2142 : RoundedTauEval :=
  evalTau precision tau2142 contact2142 logTwoBall

theorem center_sq2142 : (center2142.re : ℝ)^2 +
    (center2142.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2142]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2142 : work2142.theta.ok = true ∧
    work2142.jac.invOK = true ∧ acceptsUnitSq work2142.out = true := by decide +kernel

def cell2142 : CellCertificate where
  tauBall := tau2142
  contactCenter := center2142
  contactBall := contact2142
  work := work2142
  center_sq := center_sq2142
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2142.1
  jac_ok := checks2142.2.1
  accepted := checks2142.2.2

def tau2143 : RatBall :=
  ⟨⟨-23/320, 109/320⟩, 3/640⟩
def center2143 : GaussianRat :=
  ⟨-56463291/1000000000, 15294731/62500000⟩
def contact2143 : RatBall := localContactBall tau2143 center2143
def work2143 : RoundedTauEval :=
  evalTau precision tau2143 contact2143 logTwoBall

theorem center_sq2143 : (center2143.re : ℝ)^2 +
    (center2143.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2143]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2143 : work2143.theta.ok = true ∧
    work2143.jac.invOK = true ∧ acceptsUnitSq work2143.out = true := by decide +kernel

def cell2143 : CellCertificate where
  tauBall := tau2143
  contactCenter := center2143
  contactBall := contact2143
  work := work2143
  center_sq := center_sq2143
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2143.1
  jac_ok := checks2143.2.1
  accepted := checks2143.2.2

def cells : List CellCertificate := [cell2136, cell2137, cell2138, cell2139, cell2140, cell2141, cell2142, cell2143]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267

end


