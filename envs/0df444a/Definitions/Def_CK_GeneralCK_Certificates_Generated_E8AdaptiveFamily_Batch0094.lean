-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0094
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0094
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:31:36.112595+00:00
-- url     : https://prove2.me/theorems/1b47feda-1f10-4cd5-b4af-82e4a89cf8a5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0094.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0752 : RatBall :=
  ⟨⟨57/160, -17/160⟩, 3/320⟩
def center0752 : GaussianRat :=
  ⟨119567729/500000000, -32582953/500000000⟩
def contact0752 : RatBall := localContactBall tau0752 center0752
def work0752 : RoundedTauEval :=
  evalTau precision tau0752 contact0752 logTwoBall

theorem center_sq0752 : (center0752.re : ℝ)^2 +
    (center0752.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0752]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0752 : work0752.theta.ok = true ∧
    work0752.jac.invOK = true ∧ acceptsUnitSq work0752.out = true := by decide +kernel

def cell0752 : CellCertificate where
  tauBall := tau0752
  contactCenter := center0752
  contactBall := contact0752
  work := work0752
  center_sq := center_sq0752
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0752.1
  jac_ok := checks0752.2.1
  accepted := checks0752.2.2

def tau0753 : RatBall :=
  ⟨⟨59/160, -17/160⟩, 3/320⟩
def center0753 : GaussianRat :=
  ⟨15424847/62500000, -32309019/500000000⟩
def contact0753 : RatBall := localContactBall tau0753 center0753
def work0753 : RoundedTauEval :=
  evalTau precision tau0753 contact0753 logTwoBall

theorem center_sq0753 : (center0753.re : ℝ)^2 +
    (center0753.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0753]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0753 : work0753.theta.ok = true ∧
    work0753.jac.invOK = true ∧ acceptsUnitSq work0753.out = true := by decide +kernel

def cell0753 : CellCertificate where
  tauBall := tau0753
  contactCenter := center0753
  contactBall := contact0753
  work := work0753
  center_sq := center_sq0753
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0753.1
  jac_ok := checks0753.2.1
  accepted := checks0753.2.2

def tau0754 : RatBall :=
  ⟨⟨61/160, -19/160⟩, 3/320⟩
def center0754 : GaussianRat :=
  ⟨31873559/125000000, -7162653/100000000⟩
def contact0754 : RatBall := localContactBall tau0754 center0754
def work0754 : RoundedTauEval :=
  evalTau precision tau0754 contact0754 logTwoBall

theorem center_sq0754 : (center0754.re : ℝ)^2 +
    (center0754.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0754]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0754 : work0754.theta.ok = true ∧
    work0754.jac.invOK = true ∧ acceptsUnitSq work0754.out = true := by decide +kernel

def cell0754 : CellCertificate where
  tauBall := tau0754
  contactCenter := center0754
  contactBall := contact0754
  work := work0754
  center_sq := center_sq0754
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0754.1
  jac_ok := checks0754.2.1
  accepted := checks0754.2.2

def tau0755 : RatBall :=
  ⟨⟨61/160, -17/160⟩, 3/320⟩
def center0755 : GaussianRat :=
  ⟨254392641/1000000000, -20019/312500⟩
def contact0755 : RatBall := localContactBall tau0755 center0755
def work0755 : RoundedTauEval :=
  evalTau precision tau0755 contact0755 logTwoBall

theorem center_sq0755 : (center0755.re : ℝ)^2 +
    (center0755.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0755]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0755 : work0755.theta.ok = true ∧
    work0755.jac.invOK = true ∧ acceptsUnitSq work0755.out = true := by decide +kernel

def cell0755 : CellCertificate where
  tauBall := tau0755
  contactCenter := center0755
  contactBall := contact0755
  work := work0755
  center_sq := center_sq0755
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0755.1
  jac_ok := checks0755.2.1
  accepted := checks0755.2.2

def tau0756 : RatBall :=
  ⟨⟨57/160, -3/32⟩, 3/320⟩
def center0756 : GaussianRat :=
  ⟨11931267/50000000, -14368881/250000000⟩
def contact0756 : RatBall := localContactBall tau0756 center0756
def work0756 : RoundedTauEval :=
  evalTau precision tau0756 contact0756 logTwoBall

theorem center_sq0756 : (center0756.re : ℝ)^2 +
    (center0756.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0756]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0756 : work0756.theta.ok = true ∧
    work0756.jac.invOK = true ∧ acceptsUnitSq work0756.out = true := by decide +kernel

def cell0756 : CellCertificate where
  tauBall := tau0756
  contactCenter := center0756
  contactBall := contact0756
  work := work0756
  center_sq := center_sq0756
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0756.1
  jac_ok := checks0756.2.1
  accepted := checks0756.2.2

def tau0757 : RatBall :=
  ⟨⟨59/160, -3/32⟩, 3/320⟩
def center0757 : GaussianRat :=
  ⟨246278271/1000000000, -56993771/1000000000⟩
def contact0757 : RatBall := localContactBall tau0757 center0757
def work0757 : RoundedTauEval :=
  evalTau precision tau0757 contact0757 logTwoBall

theorem center_sq0757 : (center0757.re : ℝ)^2 +
    (center0757.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0757]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0757 : work0757.theta.ok = true ∧
    work0757.jac.invOK = true ∧ acceptsUnitSq work0757.out = true := by decide +kernel

def cell0757 : CellCertificate where
  tauBall := tau0757
  contactCenter := center0757
  contactBall := contact0757
  work := work0757
  center_sq := center_sq0757
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0757.1
  jac_ok := checks0757.2.1
  accepted := checks0757.2.2

def tau0758 : RatBall :=
  ⟨⟨57/160, -13/160⟩, 3/320⟩
def center0758 : GaussianRat :=
  ⟨238180443/1000000000, -24897027/500000000⟩
def contact0758 : RatBall := localContactBall tau0758 center0758
def work0758 : RoundedTauEval :=
  evalTau precision tau0758 contact0758 logTwoBall

theorem center_sq0758 : (center0758.re : ℝ)^2 +
    (center0758.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0758]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0758 : work0758.theta.ok = true ∧
    work0758.jac.invOK = true ∧ acceptsUnitSq work0758.out = true := by decide +kernel

def cell0758 : CellCertificate where
  tauBall := tau0758
  contactCenter := center0758
  contactBall := contact0758
  work := work0758
  center_sq := center_sq0758
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0758.1
  jac_ok := checks0758.2.1
  accepted := checks0758.2.2

def tau0759 : RatBall :=
  ⟨⟨59/160, -13/160⟩, 3/320⟩
def center0759 : GaussianRat :=
  ⟨245825343/1000000000, -12344447/250000000⟩
def contact0759 : RatBall := localContactBall tau0759 center0759
def work0759 : RoundedTauEval :=
  evalTau precision tau0759 contact0759 logTwoBall

theorem center_sq0759 : (center0759.re : ℝ)^2 +
    (center0759.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0759]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0759 : work0759.theta.ok = true ∧
    work0759.jac.invOK = true ∧ acceptsUnitSq work0759.out = true := by decide +kernel

def cell0759 : CellCertificate where
  tauBall := tau0759
  contactCenter := center0759
  contactBall := contact0759
  work := work0759
  center_sq := center_sq0759
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0759.1
  jac_ok := checks0759.2.1
  accepted := checks0759.2.2

def cells : List CellCertificate := [cell0752, cell0753, cell0754, cell0755, cell0756, cell0757, cell0758, cell0759]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094

end


