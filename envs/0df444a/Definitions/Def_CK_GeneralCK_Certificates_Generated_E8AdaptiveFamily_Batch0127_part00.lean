-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127_part00
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0127_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:33:38.560898+00:00
-- url     : https://prove2.me/theorems/fce1935f-392b-456f-8742-486afcaa0a8d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127 (part 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127 (part 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127 (part 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127 (part 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0127 (part 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau1016 : RatBall :=
  ⟨⟨9/32, 31/160⟩, 3/320⟩
def center1016 : GaussianRat :=
  ⟨19656377/100000000, 125132383/1000000000⟩
def contact1016 : RatBall := localContactBall tau1016 center1016
def work1016 : RoundedTauEval :=
  evalTau precision tau1016 contact1016 logTwoBall

theorem center_sq1016 : (center1016.re : ℝ)^2 +
    (center1016.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1016]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1016 : work1016.theta.ok = true ∧
    work1016.jac.invOK = true ∧ acceptsUnitSq work1016.out = true := by decide +kernel

def cell1016 : CellCertificate where
  tauBall := tau1016
  contactCenter := center1016
  contactBall := contact1016
  work := work1016
  center_sq := center_sq1016
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1016.1
  jac_ok := checks1016.2.1
  accepted := checks1016.2.2

def tau1017 : RatBall :=
  ⟨⟨47/160, 31/160⟩, 3/320⟩
def center1017 : GaussianRat :=
  ⟨40948189/200000000, 124226081/1000000000⟩
def contact1017 : RatBall := localContactBall tau1017 center1017
def work1017 : RoundedTauEval :=
  evalTau precision tau1017 contact1017 logTwoBall

theorem center_sq1017 : (center1017.re : ℝ)^2 +
    (center1017.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1017]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1017 : work1017.theta.ok = true ∧
    work1017.jac.invOK = true ∧ acceptsUnitSq work1017.out = true := by decide +kernel

def cell1017 : CellCertificate where
  tauBall := tau1017
  contactCenter := center1017
  contactBall := contact1017
  work := work1017
  center_sq := center_sq1017
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1017.1
  jac_ok := checks1017.2.1
  accepted := checks1017.2.2

def tau1018 : RatBall :=
  ⟨⟨53/160, 17/160⟩, 3/320⟩
def center1018 : GaussianRat :=
  ⟨44722969/200000000, 66230667/1000000000⟩
def contact1018 : RatBall := localContactBall tau1018 center1018
def work1018 : RoundedTauEval :=
  evalTau precision tau1018 contact1018 logTwoBall

theorem center_sq1018 : (center1018.re : ℝ)^2 +
    (center1018.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1018]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1018 : work1018.theta.ok = true ∧
    work1018.jac.invOK = true ∧ acceptsUnitSq work1018.out = true := by decide +kernel

def cell1018 : CellCertificate where
  tauBall := tau1018
  contactCenter := center1018
  contactBall := contact1018
  work := work1018
  center_sq := center_sq1018
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1018.1
  jac_ok := checks1018.2.1
  accepted := checks1018.2.2

def tau1019 : RatBall :=
  ⟨⟨11/32, 17/160⟩, 3/320⟩
def center1019 : GaussianRat :=
  ⟨57851871/250000000, 6570369/100000000⟩
def contact1019 : RatBall := localContactBall tau1019 center1019
def work1019 : RoundedTauEval :=
  evalTau precision tau1019 contact1019 logTwoBall

theorem center_sq1019 : (center1019.re : ℝ)^2 +
    (center1019.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1019]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1019 : work1019.theta.ok = true ∧
    work1019.jac.invOK = true ∧ acceptsUnitSq work1019.out = true := by decide +kernel

def cell1019 : CellCertificate where
  tauBall := tau1019
  contactCenter := center1019
  contactBall := contact1019
  work := work1019
  center_sq := center_sq1019
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1019.1
  jac_ok := checks1019.2.1
  accepted := checks1019.2.2

def tau1020 : RatBall :=
  ⟨⟨53/160, 19/160⟩, 3/320⟩
def center1020 : GaussianRat :=
  ⟨56041997/250000000, 74061203/1000000000⟩
def contact1020 : RatBall := localContactBall tau1020 center1020
def work1020 : RoundedTauEval :=
  evalTau precision tau1020 contact1020 logTwoBall

theorem center_sq1020 : (center1020.re : ℝ)^2 +
    (center1020.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1020]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1020 : work1020.theta.ok = true ∧
    work1020.jac.invOK = true ∧ acceptsUnitSq work1020.out = true := by decide +kernel

def cell1020 : CellCertificate where
  tauBall := tau1020
  contactCenter := center1020
  contactBall := contact1020
  work := work1020
  center_sq := center_sq1020
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1020.1
  jac_ok := checks1020.2.1
  accepted := checks1020.2.2

def tau1021 : RatBall :=
  ⟨⟨11/32, 19/160⟩, 3/320⟩
def center1021 : GaussianRat :=
  ⟨231972447/1000000000, 73469819/1000000000⟩
def contact1021 : RatBall := localContactBall tau1021 center1021
def work1021 : RoundedTauEval :=
  evalTau precision tau1021 contact1021 logTwoBall

theorem center_sq1021 : (center1021.re : ℝ)^2 +
    (center1021.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1021]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1021 : work1021.theta.ok = true ∧
    work1021.jac.invOK = true ∧ acceptsUnitSq work1021.out = true := by decide +kernel

def cell1021 : CellCertificate where
  tauBall := tau1021
  contactCenter := center1021
  contactBall := contact1021
  work := work1021
  center_sq := center_sq1021
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1021.1
  jac_ok := checks1021.2.1
  accepted := checks1021.2.2

def tau1022 : RatBall :=
  ⟨⟨49/160, 21/160⟩, 3/320⟩
def center1022 : GaussianRat :=
  ⟨41791301/200000000, 41587123/500000000⟩
def contact1022 : RatBall := localContactBall tau1022 center1022
def work1022 : RoundedTauEval :=
  evalTau precision tau1022 contact1022 logTwoBall

theorem center_sq1022 : (center1022.re : ℝ)^2 +
    (center1022.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center1022]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks1022 : work1022.theta.ok = true ∧
    work1022.jac.invOK = true ∧ acceptsUnitSq work1022.out = true := by decide +kernel

def cell1022 : CellCertificate where
  tauBall := tau1022
  contactCenter := center1022
  contactBall := contact1022
  work := work1022
  center_sq := center_sq1022
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks1022.1
  jac_ok := checks1022.2.1
  accepted := checks1022.2.2

def tau1023 : RatBall :=
  ⟨⟨51/160, 21/160⟩, 3/320⟩

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127


