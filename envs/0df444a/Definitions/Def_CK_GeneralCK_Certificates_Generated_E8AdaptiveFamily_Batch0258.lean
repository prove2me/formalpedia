-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0258
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0258
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:44:38.97248+00:00
-- url     : https://prove2.me/theorems/fc0a3569-8070-4176-b9b9-1f3ed6d2c923
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0258.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2064 : RatBall :=
  ⟨⟨-57/320, 111/320⟩, 3/640⟩
def center2064 : GaussianRat :=
  ⟨-138434183/1000000000, 120712289/500000000⟩
def contact2064 : RatBall := localContactBall tau2064 center2064
def work2064 : RoundedTauEval :=
  evalTau precision tau2064 contact2064 logTwoBall

theorem center_sq2064 : (center2064.re : ℝ)^2 +
    (center2064.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2064]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2064 : work2064.theta.ok = true ∧
    work2064.jac.invOK = true ∧ acceptsUnitSq work2064.out = true := by decide +kernel

def cell2064 : CellCertificate where
  tauBall := tau2064
  contactCenter := center2064
  contactBall := contact2064
  work := work2064
  center_sq := center_sq2064
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2064.1
  jac_ok := checks2064.2.1
  accepted := checks2064.2.2

def tau2065 : RatBall :=
  ⟨⟨-11/64, 21/64⟩, 3/640⟩
def center2065 : GaussianRat :=
  ⟨-65949739/500000000, 57017591/250000000⟩
def contact2065 : RatBall := localContactBall tau2065 center2065
def work2065 : RoundedTauEval :=
  evalTau precision tau2065 contact2065 logTwoBall

theorem center_sq2065 : (center2065.re : ℝ)^2 +
    (center2065.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2065]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2065 : work2065.theta.ok = true ∧
    work2065.jac.invOK = true ∧ acceptsUnitSq work2065.out = true := by decide +kernel

def cell2065 : CellCertificate where
  tauBall := tau2065
  contactCenter := center2065
  contactBall := contact2065
  work := work2065
  center_sq := center_sq2065
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2065.1
  jac_ok := checks2065.2.1
  accepted := checks2065.2.2

def tau2066 : RatBall :=
  ⟨⟨-53/320, 21/64⟩, 3/640⟩
def center2066 : GaussianRat :=
  ⟨-127250921/1000000000, 228652029/1000000000⟩
def contact2066 : RatBall := localContactBall tau2066 center2066
def work2066 : RoundedTauEval :=
  evalTau precision tau2066 contact2066 logTwoBall

theorem center_sq2066 : (center2066.re : ℝ)^2 +
    (center2066.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2066]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2066 : work2066.theta.ok = true ∧
    work2066.jac.invOK = true ∧ acceptsUnitSq work2066.out = true := by decide +kernel

def cell2066 : CellCertificate where
  tauBall := tau2066
  contactCenter := center2066
  contactBall := contact2066
  work := work2066
  center_sq := center_sq2066
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2066.1
  jac_ok := checks2066.2.1
  accepted := checks2066.2.2

def tau2067 : RatBall :=
  ⟨⟨-11/64, 107/320⟩, 3/640⟩
def center2067 : GaussianRat :=
  ⟨-66249189/500000000, 232719989/1000000000⟩
def contact2067 : RatBall := localContactBall tau2067 center2067
def work2067 : RoundedTauEval :=
  evalTau precision tau2067 contact2067 logTwoBall

theorem center_sq2067 : (center2067.re : ℝ)^2 +
    (center2067.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2067]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2067 : work2067.theta.ok = true ∧
    work2067.jac.invOK = true ∧ acceptsUnitSq work2067.out = true := by decide +kernel

def cell2067 : CellCertificate where
  tauBall := tau2067
  contactCenter := center2067
  contactBall := contact2067
  work := work2067
  center_sq := center_sq2067
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2067.1
  jac_ok := checks2067.2.1
  accepted := checks2067.2.2

def tau2068 : RatBall :=
  ⟨⟨-53/320, 107/320⟩, 3/640⟩
def center2068 : GaussianRat :=
  ⟨-15978923/125000000, 233317801/1000000000⟩
def contact2068 : RatBall := localContactBall tau2068 center2068
def work2068 : RoundedTauEval :=
  evalTau precision tau2068 contact2068 logTwoBall

theorem center_sq2068 : (center2068.re : ℝ)^2 +
    (center2068.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2068]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2068 : work2068.theta.ok = true ∧
    work2068.jac.invOK = true ∧ acceptsUnitSq work2068.out = true := by decide +kernel

def cell2068 : CellCertificate where
  tauBall := tau2068
  contactCenter := center2068
  contactBall := contact2068
  work := work2068
  center_sq := center_sq2068
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2068.1
  jac_ok := checks2068.2.1
  accepted := checks2068.2.2

def tau2069 : RatBall :=
  ⟨⟨-51/320, 21/64⟩, 3/640⟩
def center2069 : GaussianRat :=
  ⟨-122586619/1000000000, 229215321/1000000000⟩
def contact2069 : RatBall := localContactBall tau2069 center2069
def work2069 : RoundedTauEval :=
  evalTau precision tau2069 contact2069 logTwoBall

theorem center_sq2069 : (center2069.re : ℝ)^2 +
    (center2069.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2069]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2069 : work2069.theta.ok = true ∧
    work2069.jac.invOK = true ∧ acceptsUnitSq work2069.out = true := by decide +kernel

def cell2069 : CellCertificate where
  tauBall := tau2069
  contactCenter := center2069
  contactBall := contact2069
  work := work2069
  center_sq := center_sq2069
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2069.1
  jac_ok := checks2069.2.1
  accepted := checks2069.2.2

def tau2070 : RatBall :=
  ⟨⟨-49/320, 21/64⟩, 3/640⟩
def center2070 : GaussianRat :=
  ⟨-58953523/500000000, 57439977/250000000⟩
def contact2070 : RatBall := localContactBall tau2070 center2070
def work2070 : RoundedTauEval :=
  evalTau precision tau2070 contact2070 logTwoBall

theorem center_sq2070 : (center2070.re : ℝ)^2 +
    (center2070.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2070]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2070 : work2070.theta.ok = true ∧
    work2070.jac.invOK = true ∧ acceptsUnitSq work2070.out = true := by decide +kernel

def cell2070 : CellCertificate where
  tauBall := tau2070
  contactCenter := center2070
  contactBall := contact2070
  work := work2070
  center_sq := center_sq2070
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2070.1
  jac_ok := checks2070.2.1
  accepted := checks2070.2.2

def tau2071 : RatBall :=
  ⟨⟨-51/320, 107/320⟩, 3/640⟩
def center2071 : GaussianRat :=
  ⟨-24629661/200000000, 233896771/1000000000⟩
def contact2071 : RatBall := localContactBall tau2071 center2071
def work2071 : RoundedTauEval :=
  evalTau precision tau2071 contact2071 logTwoBall

theorem center_sq2071 : (center2071.re : ℝ)^2 +
    (center2071.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2071]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2071 : work2071.theta.ok = true ∧
    work2071.jac.invOK = true ∧ acceptsUnitSq work2071.out = true := by decide +kernel

def cell2071 : CellCertificate where
  tauBall := tau2071
  contactCenter := center2071
  contactBall := contact2071
  work := work2071
  center_sq := center_sq2071
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2071.1
  jac_ok := checks2071.2.1
  accepted := checks2071.2.2

def cells : List CellCertificate := [cell2064, cell2065, cell2066, cell2067, cell2068, cell2069, cell2070, cell2071]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258

end


