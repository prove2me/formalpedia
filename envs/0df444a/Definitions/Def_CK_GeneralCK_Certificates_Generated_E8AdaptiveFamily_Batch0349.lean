-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:12:12.991036+00:00
-- url     : https://prove2.me/theorems/9bc3dcc4-40cb-4412-abc6-849e6da3da60
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0349.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

theorem center_sq2796 : (center2796.re : ℝ)^2 +
    (center2796.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2796]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2796 : work2796.theta.ok = true ∧
    work2796.jac.invOK = true ∧ acceptsUnitSq work2796.out = true := by decide +kernel

def cell2796 : CellCertificate where
  tauBall := tau2796
  contactCenter := center2796
  contactBall := contact2796
  work := work2796
  center_sq := center_sq2796
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2796.1
  jac_ok := checks2796.2.1
  accepted := checks2796.2.2

def tau2797 : RatBall :=
  ⟨⟨-9/128, -243/640⟩, 3/1280⟩
def center2797 : GaussianRat :=
  ⟨-456897/8000000, -17236447/62500000⟩
def contact2797 : RatBall := localContactBall tau2797 center2797
def work2797 : RoundedTauEval :=
  evalTau precision tau2797 contact2797 logTwoBall

theorem center_sq2797 : (center2797.re : ℝ)^2 +
    (center2797.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2797]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2797 : work2797.theta.ok = true ∧
    work2797.jac.invOK = true ∧ acceptsUnitSq work2797.out = true := by decide +kernel

def cell2797 : CellCertificate where
  tauBall := tau2797
  contactCenter := center2797
  contactBall := contact2797
  work := work2797
  center_sq := center_sq2797
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2797.1
  jac_ok := checks2797.2.1
  accepted := checks2797.2.2

def tau2798 : RatBall :=
  ⟨⟨-47/640, -241/640⟩, 3/1280⟩
def center2798 : GaussianRat :=
  ⟨-59463601/1000000000, -273101301/1000000000⟩
def contact2798 : RatBall := localContactBall tau2798 center2798
def work2798 : RoundedTauEval :=
  evalTau precision tau2798 contact2798 logTwoBall

theorem center_sq2798 : (center2798.re : ℝ)^2 +
    (center2798.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2798]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2798 : work2798.theta.ok = true ∧
    work2798.jac.invOK = true ∧ acceptsUnitSq work2798.out = true := by decide +kernel

def cell2798 : CellCertificate where
  tauBall := tau2798
  contactCenter := center2798
  contactBall := contact2798
  work := work2798
  center_sq := center_sq2798
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2798.1
  jac_ok := checks2798.2.1
  accepted := checks2798.2.2

def tau2799 : RatBall :=
  ⟨⟨-9/128, -241/640⟩, 3/1280⟩
def center2799 : GaussianRat :=
  ⟨-11390081/200000000, -136632679/500000000⟩
def contact2799 : RatBall := localContactBall tau2799 center2799
def work2799 : RoundedTauEval :=
  evalTau precision tau2799 contact2799 logTwoBall

theorem center_sq2799 : (center2799.re : ℝ)^2 +
    (center2799.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2799]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2799 : work2799.theta.ok = true ∧
    work2799.jac.invOK = true ∧ acceptsUnitSq work2799.out = true := by decide +kernel

def cell2799 : CellCertificate where
  tauBall := tau2799
  contactCenter := center2799
  contactBall := contact2799
  work := work2799
  center_sq := center_sq2799
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2799.1
  jac_ok := checks2799.2.1
  accepted := checks2799.2.2

def cells : List CellCertificate := [cell2792, cell2793, cell2794, cell2795, cell2796, cell2797, cell2798, cell2799]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349


