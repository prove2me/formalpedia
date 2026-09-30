-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0344
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0344
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:28:42.617644+00:00
-- url     : https://prove2.me/theorems/cd71521f-d801-4fc1-8f58-348419beebbd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0344.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2752 : RatBall :=
  ⟨⟨-53/640, -49/128⟩, 3/1280⟩
def center2752 : GaussianRat :=
  ⟨-4210637/62500000, -55518211/200000000⟩
def contact2752 : RatBall := localContactBall tau2752 center2752
def work2752 : RoundedTauEval :=
  evalTau precision tau2752 contact2752 logTwoBall

theorem center_sq2752 : (center2752.re : ℝ)^2 +
    (center2752.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2752]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2752 : work2752.theta.ok = true ∧
    work2752.jac.invOK = true ∧ acceptsUnitSq work2752.out = true := by decide +kernel

def cell2752 : CellCertificate where
  tauBall := tau2752
  contactCenter := center2752
  contactBall := contact2752
  work := work2752
  center_sq := center_sq2752
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2752.1
  jac_ok := checks2752.2.1
  accepted := checks2752.2.2

def tau2753 : RatBall :=
  ⟨⟨-51/640, -247/640⟩, 3/1280⟩
def center2753 : GaussianRat :=
  ⟨-32518989/500000000, -70076353/250000000⟩
def contact2753 : RatBall := localContactBall tau2753 center2753
def work2753 : RoundedTauEval :=
  evalTau precision tau2753 contact2753 logTwoBall

theorem center_sq2753 : (center2753.re : ℝ)^2 +
    (center2753.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2753]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2753 : work2753.theta.ok = true ∧
    work2753.jac.invOK = true ∧ acceptsUnitSq work2753.out = true := by decide +kernel

def cell2753 : CellCertificate where
  tauBall := tau2753
  contactCenter := center2753
  contactBall := contact2753
  work := work2753
  center_sq := center_sq2753
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2753.1
  jac_ok := checks2753.2.1
  accepted := checks2753.2.2

def tau2754 : RatBall :=
  ⟨⟨-49/640, -247/640⟩, 3/1280⟩
def center2754 : GaussianRat :=
  ⟨-6250857/100000000, -280490707/1000000000⟩
def contact2754 : RatBall := localContactBall tau2754 center2754
def work2754 : RoundedTauEval :=
  evalTau precision tau2754 contact2754 logTwoBall

theorem center_sq2754 : (center2754.re : ℝ)^2 +
    (center2754.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2754]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2754 : work2754.theta.ok = true ∧
    work2754.jac.invOK = true ∧ acceptsUnitSq work2754.out = true := by decide +kernel

def cell2754 : CellCertificate where
  tauBall := tau2754
  contactCenter := center2754
  contactBall := contact2754
  work := work2754
  center_sq := center_sq2754
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2754.1
  jac_ok := checks2754.2.1
  accepted := checks2754.2.2

def tau2755 : RatBall :=
  ⟨⟨-51/640, -49/128⟩, 3/1280⟩
def center2755 : GaussianRat :=
  ⟨-3242521/50000000, -138890411/500000000⟩
def contact2755 : RatBall := localContactBall tau2755 center2755
def work2755 : RoundedTauEval :=
  evalTau precision tau2755 contact2755 logTwoBall

theorem center_sq2755 : (center2755.re : ℝ)^2 +
    (center2755.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2755]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2755 : work2755.theta.ok = true ∧
    work2755.jac.invOK = true ∧ acceptsUnitSq work2755.out = true := by decide +kernel

def cell2755 : CellCertificate where
  tauBall := tau2755
  contactCenter := center2755
  contactBall := contact2755
  work := work2755
  center_sq := center_sq2755
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2755.1
  jac_ok := checks2755.2.1
  accepted := checks2755.2.2

def tau2756 : RatBall :=
  ⟨⟨-49/640, -49/128⟩, 3/1280⟩
def center2756 : GaussianRat :=
  ⟨-31164041/500000000, -277963583/1000000000⟩
def contact2756 : RatBall := localContactBall tau2756 center2756
def work2756 : RoundedTauEval :=
  evalTau precision tau2756 contact2756 logTwoBall

theorem center_sq2756 : (center2756.re : ℝ)^2 +
    (center2756.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2756]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2756 : work2756.theta.ok = true ∧
    work2756.jac.invOK = true ∧ acceptsUnitSq work2756.out = true := by decide +kernel

def cell2756 : CellCertificate where
  tauBall := tau2756
  contactCenter := center2756
  contactBall := contact2756
  work := work2756
  center_sq := center_sq2756
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2756.1
  jac_ok := checks2756.2.1
  accepted := checks2756.2.2

def tau2757 : RatBall :=
  ⟨⟨-11/128, -243/640⟩, 3/1280⟩
def center2757 : GaussianRat :=
  ⟨-13937693/200000000, -54976403/200000000⟩
def contact2757 : RatBall := localContactBall tau2757 center2757
def work2757 : RoundedTauEval :=
  evalTau precision tau2757 contact2757 logTwoBall

theorem center_sq2757 : (center2757.re : ℝ)^2 +
    (center2757.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2757]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2757 : work2757.theta.ok = true ∧
    work2757.jac.invOK = true ∧ acceptsUnitSq work2757.out = true := by decide +kernel

def cell2757 : CellCertificate where
  tauBall := tau2757
  contactCenter := center2757
  contactBall := contact2757
  work := work2757
  center_sq := center_sq2757
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2757.1
  jac_ok := checks2757.2.1
  accepted := checks2757.2.2

def tau2758 : RatBall :=
  ⟨⟨-53/640, -243/640⟩, 3/1280⟩
def center2758 : GaussianRat :=
  ⟨-67178257/1000000000, -137538033/500000000⟩
def contact2758 : RatBall := localContactBall tau2758 center2758
def work2758 : RoundedTauEval :=
  evalTau precision tau2758 contact2758 logTwoBall

theorem center_sq2758 : (center2758.re : ℝ)^2 +
    (center2758.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2758]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2758 : work2758.theta.ok = true ∧
    work2758.jac.invOK = true ∧ acceptsUnitSq work2758.out = true := by decide +kernel

def cell2758 : CellCertificate where
  tauBall := tau2758
  contactCenter := center2758
  contactBall := contact2758
  work := work2758
  center_sq := center_sq2758
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2758.1
  jac_ok := checks2758.2.1
  accepted := checks2758.2.2

def tau2759 : RatBall :=
  ⟨⟨-11/128, -241/640⟩, 3/1280⟩
def center2759 : GaussianRat :=
  ⟨-34746169/500000000, -68094139/250000000⟩
def contact2759 : RatBall := localContactBall tau2759 center2759
def work2759 : RoundedTauEval :=
  evalTau precision tau2759 contact2759 logTwoBall

theorem center_sq2759 : (center2759.re : ℝ)^2 +
    (center2759.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2759]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2759 : work2759.theta.ok = true ∧
    work2759.jac.invOK = true ∧ acceptsUnitSq work2759.out = true := by decide +kernel

def cell2759 : CellCertificate where
  tauBall := tau2759
  contactCenter := center2759
  contactBall := contact2759
  work := work2759
  center_sq := center_sq2759
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2759.1
  jac_ok := checks2759.2.1
  accepted := checks2759.2.2

def cells : List CellCertificate := [cell2752, cell2753, cell2754, cell2755, cell2756, cell2757, cell2758, cell2759]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344

end


