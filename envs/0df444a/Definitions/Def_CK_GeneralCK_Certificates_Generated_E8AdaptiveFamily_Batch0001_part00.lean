-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0001_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0001_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:00:36.54595+00:00
-- url     : https://prove2.me/theorems/fdb8c0da-83d1-4093-a59c-90695aed8c9c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0001 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau0008 : RatBall :=
  ⟨⟨-1/8, -1/40⟩, 3/80⟩
def center0008 : GaussianRat :=
  ⟨-8623323/100000000, -17054997/1000000000⟩
def contact0008 : RatBall := localContactBall tau0008 center0008
def work0008 : RoundedTauEval :=
  evalTau precision tau0008 contact0008 logTwoBall

theorem center_sq0008 : (center0008.re : ℝ)^2 +
    (center0008.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0008]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0008 : work0008.theta.ok = true ∧
    work0008.jac.invOK = true ∧ acceptsUnitSq work0008.out = true := by decide +kernel

def cell0008 : CellCertificate where
  tauBall := tau0008
  contactCenter := center0008
  contactBall := contact0008
  work := work0008
  center_sq := center_sq0008
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0008.1
  jac_ok := checks0008.2.1
  accepted := checks0008.2.2

def tau0009 : RatBall :=
  ⟨⟨-3/40, -3/40⟩, 3/80⟩
def center0009 : GaussianRat :=
  ⟨-1304683/25000000, -51781961/1000000000⟩
def contact0009 : RatBall := localContactBall tau0009 center0009
def work0009 : RoundedTauEval :=
  evalTau precision tau0009 contact0009 logTwoBall

theorem center_sq0009 : (center0009.re : ℝ)^2 +
    (center0009.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0009]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0009 : work0009.theta.ok = true ∧
    work0009.jac.invOK = true ∧ acceptsUnitSq work0009.out = true := by decide +kernel

def cell0009 : CellCertificate where
  tauBall := tau0009
  contactCenter := center0009
  contactBall := contact0009
  work := work0009
  center_sq := center_sq0009
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0009.1
  jac_ok := checks0009.2.1
  accepted := checks0009.2.2

def tau0010 : RatBall :=
  ⟨⟨-1/40, -3/40⟩, 3/80⟩
def center0010 : GaussianRat :=
  ⟨-2178341/125000000, -3253349/62500000⟩
def contact0010 : RatBall := localContactBall tau0010 center0010
def work0010 : RoundedTauEval :=
  evalTau precision tau0010 contact0010 logTwoBall

theorem center_sq0010 : (center0010.re : ℝ)^2 +
    (center0010.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0010]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0010 : work0010.theta.ok = true ∧
    work0010.jac.invOK = true ∧ acceptsUnitSq work0010.out = true := by decide +kernel

def cell0010 : CellCertificate where
  tauBall := tau0010
  contactCenter := center0010
  contactBall := contact0010
  work := work0010
  center_sq := center_sq0010
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0010.1
  jac_ok := checks0010.2.1
  accepted := checks0010.2.2

def tau0011 : RatBall :=
  ⟨⟨-3/40, -1/40⟩, 3/80⟩
def center0011 : GaussianRat :=
  ⟨-51918459/1000000000, -861577/50000000⟩
def contact0011 : RatBall := localContactBall tau0011 center0011
def work0011 : RoundedTauEval :=
  evalTau precision tau0011 contact0011 logTwoBall

theorem center_sq0011 : (center0011.re : ℝ)^2 +
    (center0011.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0011]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0011 : work0011.theta.ok = true ∧
    work0011.jac.invOK = true ∧ acceptsUnitSq work0011.out = true := by decide +kernel

def cell0011 : CellCertificate where
  tauBall := tau0011
  contactCenter := center0011
  contactBall := contact0011
  work := work0011
  center_sq := center_sq0011
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0011.1
  jac_ok := checks0011.2.1
  accepted := checks0011.2.2

def tau0012 : RatBall :=
  ⟨⟨-1/40, -1/40⟩, 3/80⟩
def center0012 : GaussianRat :=
  ⟨-17336181/1000000000, -17321167/1000000000⟩
def contact0012 : RatBall := localContactBall tau0012 center0012
def work0012 : RoundedTauEval :=
  evalTau precision tau0012 contact0012 logTwoBall

theorem center_sq0012 : (center0012.re : ℝ)^2 +
    (center0012.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0012]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0012 : work0012.theta.ok = true ∧
    work0012.jac.invOK = true ∧ acceptsUnitSq work0012.out = true := by decide +kernel

def cell0012 : CellCertificate where
  tauBall := tau0012
  contactCenter := center0012
  contactBall := contact0012
  work := work0012
  center_sq := center_sq0012
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0012.1
  jac_ok := checks0012.2.1
  accepted := checks0012.2.2

def tau0013 : RatBall :=
  ⟨⟨1/40, -7/40⟩, 3/80⟩
def center0013 : GaussianRat :=
  ⟨17893761/1000000000, -7658063/62500000⟩
def contact0013 : RatBall := localContactBall tau0013 center0013
def work0013 : RoundedTauEval :=
  evalTau precision tau0013 contact0013 logTwoBall

theorem center_sq0013 : (center0013.re : ℝ)^2 +
    (center0013.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0013]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0013 : work0013.theta.ok = true ∧
    work0013.jac.invOK = true ∧ acceptsUnitSq work0013.out = true := by decide +kernel

def cell0013 : CellCertificate where
  tauBall := tau0013
  contactCenter := center0013
  contactBall := contact0013
  work := work0013
  center_sq := center_sq0013
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks0013.1
  jac_ok := checks0013.2.1
  accepted := checks0013.2.2

def tau0014 : RatBall :=
  ⟨⟨1/40, -1/8⟩, 3/80⟩
def center0014 : GaussianRat :=
  ⟨17610637/1000000000, -8705903/100000000⟩
def contact0014 : RatBall := localContactBall tau0014 center0014
def work0014 : RoundedTauEval :=
  evalTau precision tau0014 contact0014 logTwoBall

theorem center_sq0014 : (center0014.re : ℝ)^2 +
    (center0014.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center0014]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks0014 : work0014.theta.ok = true ∧
    work0014.jac.invOK = true ∧ acceptsUnitSq work0014.out = true := by decide +kernel


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0001


