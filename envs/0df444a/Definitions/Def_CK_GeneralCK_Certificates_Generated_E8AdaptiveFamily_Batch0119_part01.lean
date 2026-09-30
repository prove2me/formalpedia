-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119_part01
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:11:30.440811+00:00
-- url     : https://prove2.me/theorems/c1534c40-f38a-4544-8242-a53531d5953e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 2 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 2 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 2 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119 (part 2 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0119 (part 2 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0119_part00

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def cell0955 : CellCertificate where
  tauBall := tau0955
  contactCenter := center0955
  contactBall := contact0955
  work := work0955
  center_sq := center_sq0955
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0955.1
  jac_ok := checks0955.2.1
  accepted := checks0955.2.2

def tau0956 : RatBall :=
  ⟨⟨-3/32, 49/160⟩, 3/320⟩
def center0956 : GaussianRat :=
  ⟨-14329959/200000000, 108628837/500000000⟩
def contact0956 : RatBall := localContactBall tau0956 center0956
def work0956 : RoundedTauEval :=
  evalTau precision tau0956 contact0956 logTwoBall

theorem center_sq0956 : (center0956.re : ℝ)^2 +
    (center0956.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0956]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0956 : work0956.theta.ok = true ∧
    work0956.jac.invOK = true ∧ acceptsUnitSq work0956.out = true := by decide +kernel

def cell0956 : CellCertificate where
  tauBall := tau0956
  contactCenter := center0956
  contactBall := contact0956
  work := work0956
  center_sq := center_sq0956
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0956.1
  jac_ok := checks0956.2.1
  accepted := checks0956.2.2

def tau0957 : RatBall :=
  ⟨⟨-13/160, 49/160⟩, 3/320⟩
def center0957 : GaussianRat :=
  ⟨-3885599/62500000, 6807377/31250000⟩
def contact0957 : RatBall := localContactBall tau0957 center0957
def work0957 : RoundedTauEval :=
  evalTau precision tau0957 contact0957 logTwoBall

theorem center_sq0957 : (center0957.re : ℝ)^2 +
    (center0957.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0957]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0957 : work0957.theta.ok = true ∧
    work0957.jac.invOK = true ∧ acceptsUnitSq work0957.out = true := by decide +kernel

def cell0957 : CellCertificate where
  tauBall := tau0957
  contactCenter := center0957
  contactBall := contact0957
  work := work0957
  center_sq := center_sq0957
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0957.1
  jac_ok := checks0957.2.1
  accepted := checks0957.2.2

def tau0958 : RatBall :=
  ⟨⟨-3/32, 51/160⟩, 3/320⟩
def center0958 : GaussianRat :=
  ⟨-18071427/250000000, 113380411/500000000⟩
def contact0958 : RatBall := localContactBall tau0958 center0958
def work0958 : RoundedTauEval :=
  evalTau precision tau0958 contact0958 logTwoBall

theorem center_sq0958 : (center0958.re : ℝ)^2 +
    (center0958.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0958]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0958 : work0958.theta.ok = true ∧
    work0958.jac.invOK = true ∧ acceptsUnitSq work0958.out = true := by decide +kernel

def cell0958 : CellCertificate where
  tauBall := tau0958
  contactCenter := center0958
  contactBall := contact0958
  work := work0958
  center_sq := center_sq0958
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0958.1
  jac_ok := checks0958.2.1
  accepted := checks0958.2.2

def tau0959 : RatBall :=
  ⟨⟨-13/160, 51/160⟩, 3/320⟩
def center0959 : GaussianRat :=
  ⟨-2508961/40000000, 56843321/250000000⟩
def contact0959 : RatBall := localContactBall tau0959 center0959
def work0959 : RoundedTauEval :=
  evalTau precision tau0959 contact0959 logTwoBall

theorem center_sq0959 : (center0959.re : ℝ)^2 +
    (center0959.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0959]


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119


