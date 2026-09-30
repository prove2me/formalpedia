-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0116_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:15:28.501669+00:00
-- url     : https://prove2.me/theorems/cad8d8b2-e0e9-4b1c-bf03-937d07c63c3b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0116 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0928 : RatBall :=
  ⟨⟨-19/160, 43/160⟩, 3/320⟩
def center0928 : GaussianRat :=
  ⟨-88375401/1000000000, 188036739/1000000000⟩
def contact0928 : RatBall := localContactBall tau0928 center0928
def work0928 : RoundedTauEval :=
  evalTau precision tau0928 contact0928 logTwoBall

theorem center_sq0928 : (center0928.re : ℝ)^2 +
    (center0928.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0928]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0928 : work0928.theta.ok = true ∧
    work0928.jac.invOK = true ∧ acceptsUnitSq work0928.out = true := by decide +kernel

def cell0928 : CellCertificate where
  tauBall := tau0928
  contactCenter := center0928
  contactBall := contact0928
  work := work0928
  center_sq := center_sq0928
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0928.1
  jac_ok := checks0928.2.1
  accepted := checks0928.2.2

def tau0929 : RatBall :=
  ⟨⟨-17/160, 43/160⟩, 3/320⟩
def center0929 : GaussianRat :=
  ⟨-39590143/500000000, 47162917/250000000⟩
def contact0929 : RatBall := localContactBall tau0929 center0929
def work0929 : RoundedTauEval :=
  evalTau precision tau0929 contact0929 logTwoBall

theorem center_sq0929 : (center0929.re : ℝ)^2 +
    (center0929.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0929]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0929 : work0929.theta.ok = true ∧
    work0929.jac.invOK = true ∧ acceptsUnitSq work0929.out = true := by decide +kernel

def cell0929 : CellCertificate where
  tauBall := tau0929
  contactCenter := center0929
  contactBall := contact0929
  work := work0929
  center_sq := center_sq0929
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0929.1
  jac_ok := checks0929.2.1
  accepted := checks0929.2.2

def tau0930 : RatBall :=
  ⟨⟨-23/160, 9/32⟩, 3/320⟩
def center0930 : GaussianRat :=
  ⟨-107438161/1000000000, 195739697/1000000000⟩
def contact0930 : RatBall := localContactBall tau0930 center0930
def work0930 : RoundedTauEval :=
  evalTau precision tau0930 contact0930 logTwoBall

theorem center_sq0930 : (center0930.re : ℝ)^2 +
    (center0930.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0930]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0930 : work0930.theta.ok = true ∧
    work0930.jac.invOK = true ∧ acceptsUnitSq work0930.out = true := by decide +kernel

def cell0930 : CellCertificate where
  tauBall := tau0930
  contactCenter := center0930
  contactBall := contact0930
  work := work0930
  center_sq := center_sq0930
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0930.1
  jac_ok := checks0930.2.1
  accepted := checks0930.2.2

def tau0931 : RatBall :=
  ⟨⟨-21/160, 9/32⟩, 3/320⟩
def center0931 : GaussianRat :=
  ⟨-2456559/25000000, 19652513/100000000⟩
def contact0931 : RatBall := localContactBall tau0931 center0931
def work0931 : RoundedTauEval :=
  evalTau precision tau0931 contact0931 logTwoBall

theorem center_sq0931 : (center0931.re : ℝ)^2 +
    (center0931.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0931]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0931 : work0931.theta.ok = true ∧
    work0931.jac.invOK = true ∧ acceptsUnitSq work0931.out = true := by decide +kernel

def cell0931 : CellCertificate where
  tauBall := tau0931
  contactCenter := center0931
  contactBall := contact0931
  work := work0931
  center_sq := center_sq0931
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0931.1
  jac_ok := checks0931.2.1
  accepted := checks0931.2.2

def tau0932 : RatBall :=
  ⟨⟨-23/160, 47/160⟩, 3/320⟩
def center0932 : GaussianRat :=
  ⟨-108280123/1000000000, 204924443/1000000000⟩
def contact0932 : RatBall := localContactBall tau0932 center0932
def work0932 : RoundedTauEval :=
  evalTau precision tau0932 contact0932 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116


