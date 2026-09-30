-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0357
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0357
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:57:42.016242+00:00
-- url     : https://prove2.me/theorems/1e6746c9-b318-4330-9789-dd321a193d13
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0357.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2856 : RatBall :=
  ⟨⟨-11/640, -51/128⟩, 3/1280⟩
def center2856 : GaussianRat :=
  ⟨-3564487/250000000, -73231599/250000000⟩
def contact2856 : RatBall := localContactBall tau2856 center2856
def work2856 : RoundedTauEval :=
  evalTau precision tau2856 contact2856 logTwoBall

theorem center_sq2856 : (center2856.re : ℝ)^2 +
    (center2856.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2856]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2856 : work2856.theta.ok = true ∧
    work2856.jac.invOK = true ∧ acceptsUnitSq work2856.out = true := by decide +kernel

def cell2856 : CellCertificate where
  tauBall := tau2856
  contactCenter := center2856
  contactBall := contact2856
  work := work2856
  center_sq := center_sq2856
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2856.1
  jac_ok := checks2856.2.1
  accepted := checks2856.2.2

def tau2857 : RatBall :=
  ⟨⟨-9/640, -51/128⟩, 3/1280⟩
def center2857 : GaussianRat :=
  ⟨-11666429/1000000000, -4577599/15625000⟩
def contact2857 : RatBall := localContactBall tau2857 center2857
def work2857 : RoundedTauEval :=
  evalTau precision tau2857 contact2857 logTwoBall

theorem center_sq2857 : (center2857.re : ℝ)^2 +
    (center2857.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2857]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2857 : work2857.theta.ok = true ∧
    work2857.jac.invOK = true ∧ acceptsUnitSq work2857.out = true := by decide +kernel

def cell2857 : CellCertificate where
  tauBall := tau2857
  contactCenter := center2857
  contactBall := contact2857
  work := work2857
  center_sq := center_sq2857
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2857.1
  jac_ok := checks2857.2.1
  accepted := checks2857.2.2

def tau2858 : RatBall :=
  ⟨⟨-11/640, -253/640⟩, 3/1280⟩
def center2858 : GaussianRat :=
  ⟨-7107163/500000000, -290339131/1000000000⟩
def contact2858 : RatBall := localContactBall tau2858 center2858
def work2858 : RoundedTauEval :=
  evalTau precision tau2858 contact2858 logTwoBall

theorem center_sq2858 : (center2858.re : ℝ)^2 +
    (center2858.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2858]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2858 : work2858.theta.ok = true ∧
    work2858.jac.invOK = true ∧ acceptsUnitSq work2858.out = true := by decide +kernel

def cell2858 : CellCertificate where
  tauBall := tau2858
  contactCenter := center2858
  contactBall := contact2858
  work := work2858
  center_sq := center_sq2858
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2858.1
  jac_ok := checks2858.2.1
  accepted := checks2858.2.2

def tau2859 : RatBall :=
  ⟨⟨-9/640, -253/640⟩, 3/1280⟩
def center2859 : GaussianRat :=
  ⟨-5815363/500000000, -145189259/500000000⟩
def contact2859 : RatBall := localContactBall tau2859 center2859
def work2859 : RoundedTauEval :=
  evalTau precision tau2859 contact2859 logTwoBall

theorem center_sq2859 : (center2859.re : ℝ)^2 +
    (center2859.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2859]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2859 : work2859.theta.ok = true ∧
    work2859.jac.invOK = true ∧ acceptsUnitSq work2859.out = true := by decide +kernel

def cell2859 : CellCertificate where
  tauBall := tau2859
  contactCenter := center2859
  contactBall := contact2859
  work := work2859
  center_sq := center_sq2859
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2859.1
  jac_ok := checks2859.2.1
  accepted := checks2859.2.2

def tau2860 : RatBall :=
  ⟨⟨-3/128, -251/640⟩, 3/1280⟩
def center2860 : GaussianRat :=
  ⟨-3864199/200000000, -57531759/200000000⟩
def contact2860 : RatBall := localContactBall tau2860 center2860
def work2860 : RoundedTauEval :=
  evalTau precision tau2860 contact2860 logTwoBall

theorem center_sq2860 : (center2860.re : ℝ)^2 +
    (center2860.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2860]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2860 : work2860.theta.ok = true ∧
    work2860.jac.invOK = true ∧ acceptsUnitSq work2860.out = true := by decide +kernel

def cell2860 : CellCertificate where
  tauBall := tau2860
  contactCenter := center2860
  contactBall := contact2860
  work := work2860
  center_sq := center_sq2860
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2860.1
  jac_ok := checks2860.2.1
  accepted := checks2860.2.2

def tau2861 : RatBall :=
  ⟨⟨-13/640, -251/640⟩, 3/1280⟩
def center2861 : GaussianRat :=
  ⟨-8373251/500000000, -287713133/1000000000⟩
def contact2861 : RatBall := localContactBall tau2861 center2861
def work2861 : RoundedTauEval :=
  evalTau precision tau2861 contact2861 logTwoBall

theorem center_sq2861 : (center2861.re : ℝ)^2 +
    (center2861.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2861]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2861 : work2861.theta.ok = true ∧
    work2861.jac.invOK = true ∧ acceptsUnitSq work2861.out = true := by decide +kernel

def cell2861 : CellCertificate where
  tauBall := tau2861
  contactCenter := center2861
  contactBall := contact2861
  work := work2861
  center_sq := center_sq2861
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2861.1
  jac_ok := checks2861.2.1
  accepted := checks2861.2.2

def tau2862 : RatBall :=
  ⟨⟨-3/128, -249/640⟩, 3/1280⟩
def center2862 : GaussianRat :=
  ⟨-19263193/1000000000, -142544269/500000000⟩
def contact2862 : RatBall := localContactBall tau2862 center2862
def work2862 : RoundedTauEval :=
  evalTau precision tau2862 contact2862 logTwoBall

theorem center_sq2862 : (center2862.re : ℝ)^2 +
    (center2862.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2862]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2862 : work2862.theta.ok = true ∧
    work2862.jac.invOK = true ∧ acceptsUnitSq work2862.out = true := by decide +kernel

def cell2862 : CellCertificate where
  tauBall := tau2862
  contactCenter := center2862
  contactBall := contact2862
  work := work2862
  center_sq := center_sq2862
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2862.1
  jac_ok := checks2862.2.1
  accepted := checks2862.2.2

def tau2863 : RatBall :=
  ⟨⟨-13/640, -249/640⟩, 3/1280⟩
def center2863 : GaussianRat :=
  ⟨-3339277/200000000, -71285531/250000000⟩
def contact2863 : RatBall := localContactBall tau2863 center2863
def work2863 : RoundedTauEval :=
  evalTau precision tau2863 contact2863 logTwoBall

theorem center_sq2863 : (center2863.re : ℝ)^2 +
    (center2863.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2863]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2863 : work2863.theta.ok = true ∧
    work2863.jac.invOK = true ∧ acceptsUnitSq work2863.out = true := by decide +kernel

def cell2863 : CellCertificate where
  tauBall := tau2863
  contactCenter := center2863
  contactBall := contact2863
  work := work2863
  center_sq := center_sq2863
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2863.1
  jac_ok := checks2863.2.1
  accepted := checks2863.2.2

def cells : List CellCertificate := [cell2856, cell2857, cell2858, cell2859, cell2860, cell2861, cell2862, cell2863]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357

end


