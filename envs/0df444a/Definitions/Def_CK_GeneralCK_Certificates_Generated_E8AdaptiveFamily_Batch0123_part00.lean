-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0123_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:38:29.833097+00:00
-- url     : https://prove2.me/theorems/03659ff9-8008-4637-81a0-31590503910f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0123 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0984 : RatBall :=
  ⟨⟨-1/160, 11/32⟩, 3/320⟩
def center0984 : GaussianRat :=
  ⟨-617179/125000000, 248789139/1000000000⟩
def contact0984 : RatBall := localContactBall tau0984 center0984
def work0984 : RoundedTauEval :=
  evalTau precision tau0984 contact0984 logTwoBall

theorem center_sq0984 : (center0984.re : ℝ)^2 +
    (center0984.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0984]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0984 : work0984.theta.ok = true ∧
    work0984.jac.invOK = true ∧ acceptsUnitSq work0984.out = true := by decide +kernel

def cell0984 : CellCertificate where
  tauBall := tau0984
  contactCenter := center0984
  contactBall := contact0984
  work := work0984
  center_sq := center_sq0984
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0984.1
  jac_ok := checks0984.2.1
  accepted := checks0984.2.2

def tau0985 : RatBall :=
  ⟨⟨-1/160, 57/160⟩, 3/320⟩
def center0985 : GaussianRat :=
  ⟨-311809/62500000, 5174291/20000000⟩
def contact0985 : RatBall := localContactBall tau0985 center0985
def work0985 : RoundedTauEval :=
  evalTau precision tau0985 contact0985 logTwoBall

theorem center_sq0985 : (center0985.re : ℝ)^2 +
    (center0985.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0985]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0985 : work0985.theta.ok = true ∧
    work0985.jac.invOK = true ∧ acceptsUnitSq work0985.out = true := by decide +kernel

def cell0985 : CellCertificate where
  tauBall := tau0985
  contactCenter := center0985
  contactBall := contact0985
  work := work0985
  center_sq := center_sq0985
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0985.1
  jac_ok := checks0985.2.1
  accepted := checks0985.2.2

def tau0986 : RatBall :=
  ⟨⟨61/160, 1/32⟩, 3/320⟩
def center0986 : GaussianRat :=
  ⟨25222673/100000000, 18813147/1000000000⟩
def contact0986 : RatBall := localContactBall tau0986 center0986
def work0986 : RoundedTauEval :=
  evalTau precision tau0986 contact0986 logTwoBall

theorem center_sq0986 : (center0986.re : ℝ)^2 +
    (center0986.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0986 : work0986.theta.ok = true ∧
    work0986.jac.invOK = true ∧ acceptsUnitSq work0986.out = true := by decide +kernel

def cell0986 : CellCertificate where
  tauBall := tau0986
  contactCenter := center0986
  contactBall := contact0986
  work := work0986
  center_sq := center_sq0986
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0986.1
  jac_ok := checks0986.2.1
  accepted := checks0986.2.2

def tau0987 : RatBall :=
  ⟨⟨63/160, 1/32⟩, 3/320⟩
def center0987 : GaussianRat :=
  ⟨259721291/1000000000, 466223/25000000⟩
def contact0987 : RatBall := localContactBall tau0987 center0987
def work0987 : RoundedTauEval :=
  evalTau precision tau0987 contact0987 logTwoBall

theorem center_sq0987 : (center0987.re : ℝ)^2 +
    (center0987.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0987]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0987 : work0987.theta.ok = true ∧
    work0987.jac.invOK = true ∧ acceptsUnitSq work0987.out = true := by decide +kernel

def cell0987 : CellCertificate where
  tauBall := tau0987
  contactCenter := center0987
  contactBall := contact0987
  work := work0987
  center_sq := center_sq0987
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0987.1
  jac_ok := checks0987.2.1
  accepted := checks0987.2.2

def tau0988 : RatBall :=
  ⟨⟨61/160, 7/160⟩, 3/320⟩
def center0988 : GaussianRat :=
  ⟨252422417/1000000000, 13171007/500000000⟩
def contact0988 : RatBall := localContactBall tau0988 center0988
def work0988 : RoundedTauEval :=
  evalTau precision tau0988 contact0988 logTwoBall

theorem center_sq0988 : (center0988.re : ℝ)^2 +
    (center0988.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0988]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0988 : work0988.theta.ok = true ∧
    work0988.jac.invOK = true ∧ acceptsUnitSq work0988.out = true := by decide +kernel

def cell0988 : CellCertificate where
  tauBall := tau0988
  contactCenter := center0988
  contactBall := contact0988
  work := work0988
  center_sq := center_sq0988
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0988.1
  jac_ok := checks0988.2.1
  accepted := checks0988.2.2

def tau0989 : RatBall :=
  ⟨⟨63/160, 7/160⟩, 3/320⟩
def center0989 : GaussianRat :=
  ⟨64979987/250000000, 3263977/125000000⟩
def contact0989 : RatBall := localContactBall tau0989 center0989
def work0989 : RoundedTauEval :=
  evalTau precision tau0989 contact0989 logTwoBall

theorem center_sq0989 : (center0989.re : ℝ)^2 +
    (center0989.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0989]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0989 : work0989.theta.ok = true ∧
    work0989.jac.invOK = true ∧ acceptsUnitSq work0989.out = true := by decide +kernel

def cell0989 : CellCertificate where
  tauBall := tau0989
  contactCenter := center0989
  contactBall := contact0989
  work := work0989
  center_sq := center_sq0989
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0989.1
  jac_ok := checks0989.2.1
  accepted := checks0989.2.2

def tau0990 : RatBall :=
  ⟨⟨61/160, 9/160⟩, 3/320⟩
def center0990 : GaussianRat :=
  ⟨252683709/1000000000, 6774897/200000000⟩
def contact0990 : RatBall := localContactBall tau0990 center0990

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123


