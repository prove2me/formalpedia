-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0106
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0106
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:32:10.833871+00:00
-- url     : https://prove2.me/theorems/3e6b4ce7-2260-4a54-9835-53f55747c088
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0106.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0848 : RatBall :=
  ⟨⟨-37/160, 31/160⟩, 3/320⟩
def center0848 : GaussianRat :=
  ⟨-163226979/1000000000, 128476919/1000000000⟩
def contact0848 : RatBall := localContactBall tau0848 center0848
def work0848 : RoundedTauEval :=
  evalTau precision tau0848 contact0848 logTwoBall

theorem center_sq0848 : (center0848.re : ℝ)^2 +
    (center0848.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0848]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0848 : work0848.theta.ok = true ∧
    work0848.jac.invOK = true ∧ acceptsUnitSq work0848.out = true := by decide +kernel

def cell0848 : CellCertificate where
  tauBall := tau0848
  contactCenter := center0848
  contactBall := contact0848
  work := work0848
  center_sq := center_sq0848
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0848.1
  jac_ok := checks0848.2.1
  accepted := checks0848.2.2

def tau0849 : RatBall :=
  ⟨⟨-53/160, 33/160⟩, 3/320⟩
def center0849 : GaussianRat :=
  ⟨-114945839/500000000, 32327639/250000000⟩
def contact0849 : RatBall := localContactBall tau0849 center0849
def work0849 : RoundedTauEval :=
  evalTau precision tau0849 contact0849 logTwoBall

theorem center_sq0849 : (center0849.re : ℝ)^2 +
    (center0849.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0849]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0849 : work0849.theta.ok = true ∧
    work0849.jac.invOK = true ∧ acceptsUnitSq work0849.out = true := by decide +kernel

def cell0849 : CellCertificate where
  tauBall := tau0849
  contactCenter := center0849
  contactBall := contact0849
  work := work0849
  center_sq := center_sq0849
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0849.1
  jac_ok := checks0849.2.1
  accepted := checks0849.2.2

def tau0850 : RatBall :=
  ⟨⟨-51/160, 33/160⟩, 3/320⟩
def center0850 : GaussianRat :=
  ⟨-13868507/62500000, 13035901/100000000⟩
def contact0850 : RatBall := localContactBall tau0850 center0850
def work0850 : RoundedTauEval :=
  evalTau precision tau0850 contact0850 logTwoBall

theorem center_sq0850 : (center0850.re : ℝ)^2 +
    (center0850.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0850]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0850 : work0850.theta.ok = true ∧
    work0850.jac.invOK = true ∧ acceptsUnitSq work0850.out = true := by decide +kernel

def cell0850 : CellCertificate where
  tauBall := tau0850
  contactCenter := center0850
  contactBall := contact0850
  work := work0850
  center_sq := center_sq0850
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0850.1
  jac_ok := checks0850.2.1
  accepted := checks0850.2.2

def tau0851 : RatBall :=
  ⟨⟨-49/160, 33/160⟩, 3/320⟩
def center0851 : GaussianRat :=
  ⟨-8553183/40000000, 26276749/200000000⟩
def contact0851 : RatBall := localContactBall tau0851 center0851
def work0851 : RoundedTauEval :=
  evalTau precision tau0851 contact0851 logTwoBall

theorem center_sq0851 : (center0851.re : ℝ)^2 +
    (center0851.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0851]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0851 : work0851.theta.ok = true ∧
    work0851.jac.invOK = true ∧ acceptsUnitSq work0851.out = true := by decide +kernel

def cell0851 : CellCertificate where
  tauBall := tau0851
  contactCenter := center0851
  contactBall := contact0851
  work := work0851
  center_sq := center_sq0851
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0851.1
  jac_ok := checks0851.2.1
  accepted := checks0851.2.2

def tau0852 : RatBall :=
  ⟨⟨-51/160, 7/32⟩, 3/320⟩
def center0852 : GaussianRat :=
  ⟨-111484361/500000000, 13840239/100000000⟩
def contact0852 : RatBall := localContactBall tau0852 center0852
def work0852 : RoundedTauEval :=
  evalTau precision tau0852 contact0852 logTwoBall

theorem center_sq0852 : (center0852.re : ℝ)^2 +
    (center0852.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0852]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0852 : work0852.theta.ok = true ∧
    work0852.jac.invOK = true ∧ acceptsUnitSq work0852.out = true := by decide +kernel

def cell0852 : CellCertificate where
  tauBall := tau0852
  contactCenter := center0852
  contactBall := contact0852
  work := work0852
  center_sq := center_sq0852
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0852.1
  jac_ok := checks0852.2.1
  accepted := checks0852.2.2

def tau0853 : RatBall :=
  ⟨⟨-49/160, 7/32⟩, 3/320⟩
def center0853 : GaussianRat :=
  ⟨-26859619/125000000, 139498183/1000000000⟩
def contact0853 : RatBall := localContactBall tau0853 center0853
def work0853 : RoundedTauEval :=
  evalTau precision tau0853 contact0853 logTwoBall

theorem center_sq0853 : (center0853.re : ℝ)^2 +
    (center0853.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0853]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0853 : work0853.theta.ok = true ∧
    work0853.jac.invOK = true ∧ acceptsUnitSq work0853.out = true := by decide +kernel

def cell0853 : CellCertificate where
  tauBall := tau0853
  contactCenter := center0853
  contactBall := contact0853
  work := work0853
  center_sq := center_sq0853
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0853.1
  jac_ok := checks0853.2.1
  accepted := checks0853.2.2

def tau0854 : RatBall :=
  ⟨⟨-49/160, 37/160⟩, 3/320⟩
def center0854 : GaussianRat :=
  ⟨-8639819/40000000, 36909857/250000000⟩
def contact0854 : RatBall := localContactBall tau0854 center0854
def work0854 : RoundedTauEval :=
  evalTau precision tau0854 contact0854 logTwoBall

theorem center_sq0854 : (center0854.re : ℝ)^2 +
    (center0854.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0854]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0854 : work0854.theta.ok = true ∧
    work0854.jac.invOK = true ∧ acceptsUnitSq work0854.out = true := by decide +kernel

def cell0854 : CellCertificate where
  tauBall := tau0854
  contactCenter := center0854
  contactBall := contact0854
  work := work0854
  center_sq := center_sq0854
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0854.1
  jac_ok := checks0854.2.1
  accepted := checks0854.2.2

def tau0855 : RatBall :=
  ⟨⟨-47/160, 33/160⟩, 3/320⟩
def center0855 : GaussianRat :=
  ⟨-205693537/1000000000, 132383201/1000000000⟩
def contact0855 : RatBall := localContactBall tau0855 center0855
def work0855 : RoundedTauEval :=
  evalTau precision tau0855 contact0855 logTwoBall

theorem center_sq0855 : (center0855.re : ℝ)^2 +
    (center0855.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0855]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0855 : work0855.theta.ok = true ∧
    work0855.jac.invOK = true ∧ acceptsUnitSq work0855.out = true := by decide +kernel

def cell0855 : CellCertificate where
  tauBall := tau0855
  contactCenter := center0855
  contactBall := contact0855
  work := work0855
  center_sq := center_sq0855
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0855.1
  jac_ok := checks0855.2.1
  accepted := checks0855.2.2

def cells : List CellCertificate := [cell0848, cell0849, cell0850, cell0851, cell0852, cell0853, cell0854, cell0855]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106

end


