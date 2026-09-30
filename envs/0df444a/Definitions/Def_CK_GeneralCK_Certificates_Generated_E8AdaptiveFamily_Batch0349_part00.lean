-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0349_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:56:45.98764+00:00
-- url     : https://prove2.me/theorems/17f8cc5f-107b-469b-970b-6ea4d6324e1c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0349 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2792 : RatBall :=
  ⟨⟨-43/640, -247/640⟩, 3/1280⟩
def center2792 : GaussianRat :=
  ⟨-3431607/62500000, -70250913/250000000⟩
def contact2792 : RatBall := localContactBall tau2792 center2792
def work2792 : RoundedTauEval :=
  evalTau precision tau2792 contact2792 logTwoBall

theorem center_sq2792 : (center2792.re : ℝ)^2 +
    (center2792.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2792]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2792 : work2792.theta.ok = true ∧
    work2792.jac.invOK = true ∧ acceptsUnitSq work2792.out = true := by decide +kernel

def cell2792 : CellCertificate where
  tauBall := tau2792
  contactCenter := center2792
  contactBall := contact2792
  work := work2792
  center_sq := center_sq2792
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2792.1
  jac_ok := checks2792.2.1
  accepted := checks2792.2.2

def tau2793 : RatBall :=
  ⟨⟨-41/640, -247/640⟩, 3/1280⟩
def center2793 : GaussianRat :=
  ⟨-52366871/1000000000, -70290053/250000000⟩
def contact2793 : RatBall := localContactBall tau2793 center2793
def work2793 : RoundedTauEval :=
  evalTau precision tau2793 contact2793 logTwoBall

theorem center_sq2793 : (center2793.re : ℝ)^2 +
    (center2793.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2793]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2793 : work2793.theta.ok = true ∧
    work2793.jac.invOK = true ∧ acceptsUnitSq work2793.out = true := by decide +kernel

def cell2793 : CellCertificate where
  tauBall := tau2793
  contactCenter := center2793
  contactBall := contact2793
  work := work2793
  center_sq := center_sq2793
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2793.1
  jac_ok := checks2793.2.1
  accepted := checks2793.2.2

def tau2794 : RatBall :=
  ⟨⟨-43/640, -49/128⟩, 3/1280⟩
def center2794 : GaussianRat :=
  ⟨-6843329/125000000, -556939/2000000⟩
def contact2794 : RatBall := localContactBall tau2794 center2794
def work2794 : RoundedTauEval :=
  evalTau precision tau2794 contact2794 logTwoBall

theorem center_sq2794 : (center2794.re : ℝ)^2 +
    (center2794.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2794]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2794 : work2794.theta.ok = true ∧
    work2794.jac.invOK = true ∧ acceptsUnitSq work2794.out = true := by decide +kernel

def cell2794 : CellCertificate where
  tauBall := tau2794
  contactCenter := center2794
  contactBall := contact2794
  work := work2794
  center_sq := center_sq2794
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2794.1
  jac_ok := checks2794.2.1
  accepted := checks2794.2.2

def tau2795 : RatBall :=
  ⟨⟨-41/640, -49/128⟩, 3/1280⟩
def center2795 : GaussianRat :=
  ⟨-13053747/250000000, -34827989/125000000⟩
def contact2795 : RatBall := localContactBall tau2795 center2795
def work2795 : RoundedTauEval :=
  evalTau precision tau2795 contact2795 logTwoBall

theorem center_sq2795 : (center2795.re : ℝ)^2 +
    (center2795.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2795]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2795 : work2795.theta.ok = true ∧
    work2795.jac.invOK = true ∧ acceptsUnitSq work2795.out = true := by decide +kernel

def cell2795 : CellCertificate where
  tauBall := tau2795
  contactCenter := center2795
  contactBall := contact2795
  work := work2795
  center_sq := center_sq2795
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2795.1
  jac_ok := checks2795.2.1
  accepted := checks2795.2.2

def tau2796 : RatBall :=
  ⟨⟨-47/640, -243/640⟩, 3/1280⟩
def center2796 : GaussianRat :=
  ⟨-59632267/1000000000, -137808407/500000000⟩
def contact2796 : RatBall := localContactBall tau2796 center2796
def work2796 : RoundedTauEval :=
  evalTau precision tau2796 contact2796 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349


