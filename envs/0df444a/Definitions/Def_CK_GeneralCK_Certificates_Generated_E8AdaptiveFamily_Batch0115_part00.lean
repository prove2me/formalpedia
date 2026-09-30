-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0115_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:50.348638+00:00
-- url     : https://prove2.me/theorems/929bdd7d-3275-434e-bbd7-515e650801ce
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0115 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0920 : RatBall :=
  ⟨⟨-27/160, 47/160⟩, 3/320⟩
def center0920 : GaussianRat :=
  ⟨-31652671/250000000, 101529593/500000000⟩
def contact0920 : RatBall := localContactBall tau0920 center0920
def work0920 : RoundedTauEval :=
  evalTau precision tau0920 contact0920 logTwoBall

theorem center_sq0920 : (center0920.re : ℝ)^2 +
    (center0920.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0920]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0920 : work0920.theta.ok = true ∧
    work0920.jac.invOK = true ∧ acceptsUnitSq work0920.out = true := by decide +kernel

def cell0920 : CellCertificate where
  tauBall := tau0920
  contactCenter := center0920
  contactBall := contact0920
  work := work0920
  center_sq := center_sq0920
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0920.1
  jac_ok := checks0920.2.1
  accepted := checks0920.2.2

def tau0921 : RatBall :=
  ⟨⟨-5/32, 47/160⟩, 3/320⟩
def center0921 : GaussianRat :=
  ⟨-58736127/500000000, 40804889/200000000⟩
def contact0921 : RatBall := localContactBall tau0921 center0921
def work0921 : RoundedTauEval :=
  evalTau precision tau0921 contact0921 logTwoBall

theorem center_sq0921 : (center0921.re : ℝ)^2 +
    (center0921.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0921]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0921 : work0921.theta.ok = true ∧
    work0921.jac.invOK = true ∧ acceptsUnitSq work0921.out = true := by decide +kernel

def cell0921 : CellCertificate where
  tauBall := tau0921
  contactCenter := center0921
  contactBall := contact0921
  work := work0921
  center_sq := center_sq0921
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0921.1
  jac_ok := checks0921.2.1
  accepted := checks0921.2.2

def tau0922 : RatBall :=
  ⟨⟨-23/160, 41/160⟩, 3/320⟩
def center0922 : GaussianRat :=
  ⟨-105897059/1000000000, 22194707/125000000⟩
def contact0922 : RatBall := localContactBall tau0922 center0922
def work0922 : RoundedTauEval :=
  evalTau precision tau0922 contact0922 logTwoBall

theorem center_sq0922 : (center0922.re : ℝ)^2 +
    (center0922.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0922]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0922 : work0922.theta.ok = true ∧
    work0922.jac.invOK = true ∧ acceptsUnitSq work0922.out = true := by decide +kernel

def cell0922 : CellCertificate where
  tauBall := tau0922
  contactCenter := center0922
  contactBall := contact0922
  work := work0922
  center_sq := center_sq0922
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0922.1
  jac_ok := checks0922.2.1
  accepted := checks0922.2.2

def tau0923 : RatBall :=
  ⟨⟨-21/160, 41/160⟩, 3/320⟩
def center0923 : GaussianRat :=
  ⟨-96843181/1000000000, 5570429/31250000⟩
def contact0923 : RatBall := localContactBall tau0923 center0923
def work0923 : RoundedTauEval :=
  evalTau precision tau0923 contact0923 logTwoBall

theorem center_sq0923 : (center0923.re : ℝ)^2 +
    (center0923.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0923]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0923 : work0923.theta.ok = true ∧
    work0923.jac.invOK = true ∧ acceptsUnitSq work0923.out = true := by decide +kernel

def cell0923 : CellCertificate where
  tauBall := tau0923
  contactCenter := center0923
  contactBall := contact0923
  work := work0923
  center_sq := center_sq0923
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0923.1
  jac_ok := checks0923.2.1
  accepted := checks0923.2.2

def tau0924 : RatBall :=
  ⟨⟨-23/160, 43/160⟩, 3/320⟩
def center0924 : GaussianRat :=
  ⟨-106644393/1000000000, 93309307/500000000⟩
def contact0924 : RatBall := localContactBall tau0924 center0924
def work0924 : RoundedTauEval :=
  evalTau precision tau0924 contact0924 logTwoBall

theorem center_sq0924 : (center0924.re : ℝ)^2 +
    (center0924.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0924]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0924 : work0924.theta.ok = true ∧
    work0924.jac.invOK = true ∧ acceptsUnitSq work0924.out = true := by decide +kernel

def cell0924 : CellCertificate where
  tauBall := tau0924
  contactCenter := center0924
  contactBall := contact0924
  work := work0924
  center_sq := center_sq0924
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0924.1
  jac_ok := checks0924.2.1
  accepted := checks0924.2.2

def tau0925 : RatBall :=
  ⟨⟨-21/160, 43/160⟩, 3/320⟩
def center0925 : GaussianRat :=
  ⟨-1523927/15625000, 46839637/250000000⟩
def contact0925 : RatBall := localContactBall tau0925 center0925
def work0925 : RoundedTauEval :=
  evalTau precision tau0925 contact0925 logTwoBall

theorem center_sq0925 : (center0925.re : ℝ)^2 +
    (center0925.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0925]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0925 : work0925.theta.ok = true ∧
    work0925.jac.invOK = true ∧ acceptsUnitSq work0925.out = true := by decide +kernel

def cell0925 : CellCertificate where
  tauBall := tau0925
  contactCenter := center0925
  contactBall := contact0925
  work := work0925
  center_sq := center_sq0925
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0925.1
  jac_ok := checks0925.2.1
  accepted := checks0925.2.2

def tau0926 : RatBall :=
  ⟨⟨-19/160, 41/160⟩, 3/320⟩
def center0926 : GaussianRat :=
  ⟨-43873979/500000000, 35778323/200000000⟩
def contact0926 : RatBall := localContactBall tau0926 center0926
def work0926 : RoundedTauEval :=
  evalTau precision tau0926 contact0926 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115


