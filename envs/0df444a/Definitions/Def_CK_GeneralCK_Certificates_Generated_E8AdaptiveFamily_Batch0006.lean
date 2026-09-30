-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0006
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0006
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:23:05.792995+00:00
-- url     : https://prove2.me/theorems/9f2d845e-7f3a-477c-a071-c18e4813bbad
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0006.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0048 : RatBall :=
  ⟨⟨3/40, 1/8⟩, 3/80⟩
def center0048 : GaussianRat :=
  ⟨52733271/1000000000, 10824621/125000000⟩
def contact0048 : RatBall := localContactBall tau0048 center0048
def work0048 : RoundedTauEval :=
  evalTau precision tau0048 contact0048 logTwoBall

theorem center_sq0048 : (center0048.re : ℝ)^2 +
    (center0048.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0048]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0048 : work0048.theta.ok = true ∧
    work0048.jac.invOK = true ∧ acceptsUnitSq work0048.out = true := by decide +kernel

def cell0048 : CellCertificate where
  tauBall := tau0048
  contactCenter := center0048
  contactBall := contact0048
  work := work0048
  center_sq := center_sq0048
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0048.1
  jac_ok := checks0048.2.1
  accepted := checks0048.2.2

def tau0049 : RatBall :=
  ⟨⟨1/40, 7/40⟩, 3/80⟩
def center0049 : GaussianRat :=
  ⟨17893761/1000000000, 7658063/62500000⟩
def contact0049 : RatBall := localContactBall tau0049 center0049
def work0049 : RoundedTauEval :=
  evalTau precision tau0049 contact0049 logTwoBall

theorem center_sq0049 : (center0049.re : ℝ)^2 +
    (center0049.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0049]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0049 : work0049.theta.ok = true ∧
    work0049.jac.invOK = true ∧ acceptsUnitSq work0049.out = true := by decide +kernel

def cell0049 : CellCertificate where
  tauBall := tau0049
  contactCenter := center0049
  contactBall := contact0049
  work := work0049
  center_sq := center_sq0049
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0049.1
  jac_ok := checks0049.2.1
  accepted := checks0049.2.2

def tau0050 : RatBall :=
  ⟨⟨1/8, 1/8⟩, 3/80⟩
def center0050 : GaussianRat :=
  ⟨87563403/1000000000, 85687457/1000000000⟩
def contact0050 : RatBall := localContactBall tau0050 center0050
def work0050 : RoundedTauEval :=
  evalTau precision tau0050 contact0050 logTwoBall

theorem center_sq0050 : (center0050.re : ℝ)^2 +
    (center0050.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0050]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0050 : work0050.theta.ok = true ∧
    work0050.jac.invOK = true ∧ acceptsUnitSq work0050.out = true := by decide +kernel

def cell0050 : CellCertificate where
  tauBall := tau0050
  contactCenter := center0050
  contactBall := contact0050
  work := work0050
  center_sq := center_sq0050
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0050.1
  jac_ok := checks0050.2.1
  accepted := checks0050.2.2

def tau0051 : RatBall :=
  ⟨⟨9/40, 1/40⟩, 3/80⟩
def center0051 : GaussianRat :=
  ⟨76697679/500000000, 4116037/250000000⟩
def contact0051 : RatBall := localContactBall tau0051 center0051
def work0051 : RoundedTauEval :=
  evalTau precision tau0051 contact0051 logTwoBall

theorem center_sq0051 : (center0051.re : ℝ)^2 +
    (center0051.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0051]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0051 : work0051.theta.ok = true ∧
    work0051.jac.invOK = true ∧ acceptsUnitSq work0051.out = true := by decide +kernel

def cell0051 : CellCertificate where
  tauBall := tau0051
  contactCenter := center0051
  contactBall := contact0051
  work := work0051
  center_sq := center_sq0051
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0051.1
  jac_ok := checks0051.2.1
  accepted := checks0051.2.2

def tau0052 : RatBall :=
  ⟨⟨-3/16, -17/80⟩, 3/160⟩
def center0052 : GaussianRat :=
  ⟨-16793263/125000000, -143981719/1000000000⟩
def contact0052 : RatBall := localContactBall tau0052 center0052
def work0052 : RoundedTauEval :=
  evalTau precision tau0052 contact0052 logTwoBall

theorem center_sq0052 : (center0052.re : ℝ)^2 +
    (center0052.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0052]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0052 : work0052.theta.ok = true ∧
    work0052.jac.invOK = true ∧ acceptsUnitSq work0052.out = true := by decide +kernel

def cell0052 : CellCertificate where
  tauBall := tau0052
  contactCenter := center0052
  contactBall := contact0052
  work := work0052
  center_sq := center_sq0052
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0052.1
  jac_ok := checks0052.2.1
  accepted := checks0052.2.2

def tau0053 : RatBall :=
  ⟨⟨-13/80, -17/80⟩, 3/160⟩
def center0053 : GaussianRat :=
  ⟨-58429249/500000000, -145353777/1000000000⟩
def contact0053 : RatBall := localContactBall tau0053 center0053
def work0053 : RoundedTauEval :=
  evalTau precision tau0053 contact0053 logTwoBall

theorem center_sq0053 : (center0053.re : ℝ)^2 +
    (center0053.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0053]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0053 : work0053.theta.ok = true ∧
    work0053.jac.invOK = true ∧ acceptsUnitSq work0053.out = true := by decide +kernel

def cell0053 : CellCertificate where
  tauBall := tau0053
  contactCenter := center0053
  contactBall := contact0053
  work := work0053
  center_sq := center_sq0053
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0053.1
  jac_ok := checks0053.2.1
  accepted := checks0053.2.2

def tau0054 : RatBall :=
  ⟨⟨-11/80, -19/80⟩, 3/160⟩
def center0054 : GaussianRat :=
  ⟨-25094739/250000000, -82197279/500000000⟩
def contact0054 : RatBall := localContactBall tau0054 center0054
def work0054 : RoundedTauEval :=
  evalTau precision tau0054 contact0054 logTwoBall

theorem center_sq0054 : (center0054.re : ℝ)^2 +
    (center0054.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0054]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0054 : work0054.theta.ok = true ∧
    work0054.jac.invOK = true ∧ acceptsUnitSq work0054.out = true := by decide +kernel

def cell0054 : CellCertificate where
  tauBall := tau0054
  contactCenter := center0054
  contactBall := contact0054
  work := work0054
  center_sq := center_sq0054
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0054.1
  jac_ok := checks0054.2.1
  accepted := checks0054.2.2

def tau0055 : RatBall :=
  ⟨⟨-9/80, -19/80⟩, 3/160⟩
def center0055 : GaussianRat :=
  ⟨-20589547/250000000, -33110861/200000000⟩
def contact0055 : RatBall := localContactBall tau0055 center0055
def work0055 : RoundedTauEval :=
  evalTau precision tau0055 contact0055 logTwoBall

theorem center_sq0055 : (center0055.re : ℝ)^2 +
    (center0055.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0055]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0055 : work0055.theta.ok = true ∧
    work0055.jac.invOK = true ∧ acceptsUnitSq work0055.out = true := by decide +kernel

def cell0055 : CellCertificate where
  tauBall := tau0055
  contactCenter := center0055
  contactBall := contact0055
  work := work0055
  center_sq := center_sq0055
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0055.1
  jac_ok := checks0055.2.1
  accepted := checks0055.2.2

def cells : List CellCertificate := [cell0048, cell0049, cell0050, cell0051, cell0052, cell0053, cell0054, cell0055]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006

end


