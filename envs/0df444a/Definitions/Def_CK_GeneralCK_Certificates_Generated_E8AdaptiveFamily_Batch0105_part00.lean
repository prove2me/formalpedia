-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0105_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:19:37.734569+00:00
-- url     : https://prove2.me/theorems/f45ec3e9-a6e0-4c4d-9036-eb7cfcbf3679
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0105 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0840 : RatBall :=
  ⟨⟨-9/32, 31/160⟩, 3/320⟩
def center0840 : GaussianRat :=
  ⟨-19656377/100000000, 125132383/1000000000⟩
def contact0840 : RatBall := localContactBall tau0840 center0840
def work0840 : RoundedTauEval :=
  evalTau precision tau0840 contact0840 logTwoBall

theorem center_sq0840 : (center0840.re : ℝ)^2 +
    (center0840.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0840]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0840 : work0840.theta.ok = true ∧
    work0840.jac.invOK = true ∧ acceptsUnitSq work0840.out = true := by decide +kernel

def cell0840 : CellCertificate where
  tauBall := tau0840
  contactCenter := center0840
  contactBall := contact0840
  work := work0840
  center_sq := center_sq0840
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0840.1
  jac_ok := checks0840.2.1
  accepted := checks0840.2.2

def tau0841 : RatBall :=
  ⟨⟨-43/160, 29/160⟩, 3/320⟩
def center0841 : GaussianRat :=
  ⟨-187487239/1000000000, 23550431/200000000⟩
def contact0841 : RatBall := localContactBall tau0841 center0841
def work0841 : RoundedTauEval :=
  evalTau precision tau0841 contact0841 logTwoBall

theorem center_sq0841 : (center0841.re : ℝ)^2 +
    (center0841.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0841]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0841 : work0841.theta.ok = true ∧
    work0841.jac.invOK = true ∧ acceptsUnitSq work0841.out = true := by decide +kernel

def cell0841 : CellCertificate where
  tauBall := tau0841
  contactCenter := center0841
  contactBall := contact0841
  work := work0841
  center_sq := center_sq0841
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0841.1
  jac_ok := checks0841.2.1
  accepted := checks0841.2.2

def tau0842 : RatBall :=
  ⟨⟨-41/160, 29/160⟩, 3/320⟩
def center0842 : GaussianRat :=
  ⟨-89605161/500000000, 4741701/40000000⟩
def contact0842 : RatBall := localContactBall tau0842 center0842
def work0842 : RoundedTauEval :=
  evalTau precision tau0842 contact0842 logTwoBall

theorem center_sq0842 : (center0842.re : ℝ)^2 +
    (center0842.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0842]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0842 : work0842.theta.ok = true ∧
    work0842.jac.invOK = true ∧ acceptsUnitSq work0842.out = true := by decide +kernel

def cell0842 : CellCertificate where
  tauBall := tau0842
  contactCenter := center0842
  contactBall := contact0842
  work := work0842
  center_sq := center_sq0842
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0842.1
  jac_ok := checks0842.2.1
  accepted := checks0842.2.2

def tau0843 : RatBall :=
  ⟨⟨-43/160, 31/160⟩, 3/320⟩
def center0843 : GaussianRat :=
  ⟨-188321901/1000000000, 126012049/1000000000⟩
def contact0843 : RatBall := localContactBall tau0843 center0843
def work0843 : RoundedTauEval :=
  evalTau precision tau0843 contact0843 logTwoBall

theorem center_sq0843 : (center0843.re : ℝ)^2 +
    (center0843.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0843]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0843 : work0843.theta.ok = true ∧
    work0843.jac.invOK = true ∧ acceptsUnitSq work0843.out = true := by decide +kernel

def cell0843 : CellCertificate where
  tauBall := tau0843
  contactCenter := center0843
  contactBall := contact0843
  work := work0843
  center_sq := center_sq0843
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0843.1
  jac_ok := checks0843.2.1
  accepted := checks0843.2.2

def tau0844 : RatBall :=
  ⟨⟨-41/160, 31/160⟩, 3/320⟩
def center0844 : GaussianRat :=
  ⟨-36003433/200000000, 3171591/25000000⟩
def contact0844 : RatBall := localContactBall tau0844 center0844
def work0844 : RoundedTauEval :=
  evalTau precision tau0844 contact0844 logTwoBall

theorem center_sq0844 : (center0844.re : ℝ)^2 +
    (center0844.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0844]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0844 : work0844.theta.ok = true ∧
    work0844.jac.invOK = true ∧ acceptsUnitSq work0844.out = true := by decide +kernel

def cell0844 : CellCertificate where
  tauBall := tau0844
  contactCenter := center0844
  contactBall := contact0844
  work := work0844
  center_sq := center_sq0844
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0844.1
  jac_ok := checks0844.2.1
  accepted := checks0844.2.2

def tau0845 : RatBall :=
  ⟨⟨-39/160, 29/160⟩, 3/320⟩
def center0845 : GaussianRat :=
  ⟨-2135923/12500000, 119305389/1000000000⟩
def contact0845 : RatBall := localContactBall tau0845 center0845
def work0845 : RoundedTauEval :=
  evalTau precision tau0845 contact0845 logTwoBall

theorem center_sq0845 : (center0845.re : ℝ)^2 +
    (center0845.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0845]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0845 : work0845.theta.ok = true ∧
    work0845.jac.invOK = true ∧ acceptsUnitSq work0845.out = true := by decide +kernel

def cell0845 : CellCertificate where
  tauBall := tau0845
  contactCenter := center0845
  contactBall := contact0845
  work := work0845
  center_sq := center_sq0845
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0845.1
  jac_ok := checks0845.2.1
  accepted := checks0845.2.2

def tau0846 : RatBall :=
  ⟨⟨-37/160, 29/160⟩, 3/320⟩
def center0846 : GaussianRat :=
  ⟨-81239917/500000000, 60019727/500000000⟩
def contact0846 : RatBall := localContactBall tau0846 center0846
def work0846 : RoundedTauEval :=
  evalTau precision tau0846 contact0846 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105


