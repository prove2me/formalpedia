-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0376_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:20:46.459228+00:00
-- url     : https://prove2.me/theorems/2f7ee19b-85b6-41c1-8d2e-7cc6c6aaed26
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0376 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3008 : RatBall :=
  ⟨⟨11/128, -251/640⟩, 3/1280⟩
def center3008 : GaussianRat :=
  ⟨70500491/1000000000, -35621651/125000000⟩
def contact3008 : RatBall := localContactBall tau3008 center3008
def work3008 : RoundedTauEval :=
  evalTau precision tau3008 contact3008 logTwoBall

theorem center_sq3008 : (center3008.re : ℝ)^2 +
    (center3008.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3008]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3008 : work3008.theta.ok = true ∧
    work3008.jac.invOK = true ∧ acceptsUnitSq work3008.out = true := by decide +kernel

def cell3008 : CellCertificate where
  tauBall := tau3008
  contactCenter := center3008
  contactBall := contact3008
  work := work3008
  center_sq := center_sq3008
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3008.1
  jac_ok := checks3008.2.1
  accepted := checks3008.2.2

def tau3009 : RatBall :=
  ⟨⟨53/640, -249/640⟩, 3/1280⟩
def center3009 : GaussianRat :=
  ⟨33881037/500000000, -282642041/1000000000⟩
def contact3009 : RatBall := localContactBall tau3009 center3009
def work3009 : RoundedTauEval :=
  evalTau precision tau3009 contact3009 logTwoBall

theorem center_sq3009 : (center3009.re : ℝ)^2 +
    (center3009.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3009]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3009 : work3009.theta.ok = true ∧
    work3009.jac.invOK = true ∧ acceptsUnitSq work3009.out = true := by decide +kernel

def cell3009 : CellCertificate where
  tauBall := tau3009
  contactCenter := center3009
  contactBall := contact3009
  work := work3009
  center_sq := center_sq3009
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3009.1
  jac_ok := checks3009.2.1
  accepted := checks3009.2.2

def tau3010 : RatBall :=
  ⟨⟨11/128, -249/640⟩, 3/1280⟩
def center3010 : GaussianRat :=
  ⟨70293283/1000000000, -14121991/50000000⟩
def contact3010 : RatBall := localContactBall tau3010 center3010
def work3010 : RoundedTauEval :=
  evalTau precision tau3010 contact3010 logTwoBall

theorem center_sq3010 : (center3010.re : ℝ)^2 +
    (center3010.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3010]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3010 : work3010.theta.ok = true ∧
    work3010.jac.invOK = true ∧ acceptsUnitSq work3010.out = true := by decide +kernel

def cell3010 : CellCertificate where
  tauBall := tau3010
  contactCenter := center3010
  contactBall := contact3010
  work := work3010
  center_sq := center_sq3010
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3010.1
  jac_ok := checks3010.2.1
  accepted := checks3010.2.2

def tau3011 : RatBall :=
  ⟨⟨57/640, -249/640⟩, 3/1280⟩
def center3011 : GaussianRat :=
  ⟨14564333/200000000, -70557619/250000000⟩
def contact3011 : RatBall := localContactBall tau3011 center3011
def work3011 : RoundedTauEval :=
  evalTau precision tau3011 contact3011 logTwoBall

theorem center_sq3011 : (center3011.re : ℝ)^2 +
    (center3011.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3011]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3011 : work3011.theta.ok = true ∧
    work3011.jac.invOK = true ∧ acceptsUnitSq work3011.out = true := by decide +kernel

def cell3011 : CellCertificate where
  tauBall := tau3011
  contactCenter := center3011
  contactBall := contact3011
  work := work3011
  center_sq := center_sq3011
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3011.1
  jac_ok := checks3011.2.1
  accepted := checks3011.2.2

def tau3012 : RatBall :=
  ⟨⟨59/640, -249/640⟩, 3/1280⟩
def center3012 : GaussianRat :=
  ⟨75347127/1000000000, -8812939/31250000⟩
def contact3012 : RatBall := localContactBall tau3012 center3012
def work3012 : RoundedTauEval :=
  evalTau precision tau3012 contact3012 logTwoBall

theorem center_sq3012 : (center3012.re : ℝ)^2 +
    (center3012.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3012]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3012 : work3012.theta.ok = true ∧
    work3012.jac.invOK = true ∧ acceptsUnitSq work3012.out = true := by decide +kernel

def cell3012 : CellCertificate where
  tauBall := tau3012
  contactCenter := center3012
  contactBall := contact3012
  work := work3012
  center_sq := center_sq3012
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3012.1
  jac_ok := checks3012.2.1
  accepted := checks3012.2.2

def tau3013 : RatBall :=
  ⟨⟨61/640, -249/640⟩, 3/1280⟩
def center3013 : GaussianRat :=
  ⟨38934787/500000000, -281790577/1000000000⟩
def contact3013 : RatBall := localContactBall tau3013 center3013
def work3013 : RoundedTauEval :=
  evalTau precision tau3013 contact3013 logTwoBall

theorem center_sq3013 : (center3013.re : ℝ)^2 +
    (center3013.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3013]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3013 : work3013.theta.ok = true ∧
    work3013.jac.invOK = true ∧ acceptsUnitSq work3013.out = true := by decide +kernel

def cell3013 : CellCertificate where
  tauBall := tau3013
  contactCenter := center3013
  contactBall := contact3013
  work := work3013
  center_sq := center_sq3013
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3013.1
  jac_ok := checks3013.2.1
  accepted := checks3013.2.2

def tau3014 : RatBall :=
  ⟨⟨63/640, -249/640⟩, 3/1280⟩
def center3014 : GaussianRat :=
  ⟨16077783/200000000, -281560103/1000000000⟩
def contact3014 : RatBall := localContactBall tau3014 center3014
def work3014 : RoundedTauEval :=
  evalTau precision tau3014 contact3014 logTwoBall


end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376


