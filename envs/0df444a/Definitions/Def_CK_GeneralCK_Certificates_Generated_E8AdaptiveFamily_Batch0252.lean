-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0252
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0252
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T16:52:46.928674+00:00
-- url     : https://prove2.me/theorems/5420bef5-85ac-4806-9f96-3935ad224075
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0252.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2016 : RatBall :=
  ⟨⟨-13/64, 101/320⟩, 3/640⟩
def center2016 : GaussianRat :=
  ⟨-38393397/250000000, 26977781/125000000⟩
def contact2016 : RatBall := localContactBall tau2016 center2016
def work2016 : RoundedTauEval :=
  evalTau precision tau2016 contact2016 logTwoBall

theorem center_sq2016 : (center2016.re : ℝ)^2 +
    (center2016.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2016]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2016 : work2016.theta.ok = true ∧
    work2016.jac.invOK = true ∧ acceptsUnitSq work2016.out = true := by decide +kernel

def cell2016 : CellCertificate where
  tauBall := tau2016
  contactCenter := center2016
  contactBall := contact2016
  work := work2016
  center_sq := center_sq2016
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2016.1
  jac_ok := checks2016.2.1
  accepted := checks2016.2.2

def tau2017 : RatBall :=
  ⟨⟨-67/320, 103/320⟩, 3/640⟩
def center2017 : GaussianRat :=
  ⟨-79376053/500000000, 109843089/500000000⟩
def contact2017 : RatBall := localContactBall tau2017 center2017
def work2017 : RoundedTauEval :=
  evalTau precision tau2017 contact2017 logTwoBall

theorem center_sq2017 : (center2017.re : ℝ)^2 +
    (center2017.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2017]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2017 : work2017.theta.ok = true ∧
    work2017.jac.invOK = true ∧ acceptsUnitSq work2017.out = true := by decide +kernel

def cell2017 : CellCertificate where
  tauBall := tau2017
  contactCenter := center2017
  contactBall := contact2017
  work := work2017
  center_sq := center_sq2017
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2017.1
  jac_ok := checks2017.2.1
  accepted := checks2017.2.2

def tau2018 : RatBall :=
  ⟨⟨-13/64, 103/320⟩, 3/640⟩
def center2018 : GaussianRat :=
  ⟨-154223071/1000000000, 110176223/500000000⟩
def contact2018 : RatBall := localContactBall tau2018 center2018
def work2018 : RoundedTauEval :=
  evalTau precision tau2018 contact2018 logTwoBall

theorem center_sq2018 : (center2018.re : ℝ)^2 +
    (center2018.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2018]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2018 : work2018.theta.ok = true ∧
    work2018.jac.invOK = true ∧ acceptsUnitSq work2018.out = true := by decide +kernel

def cell2018 : CellCertificate where
  tauBall := tau2018
  contactCenter := center2018
  contactBall := contact2018
  work := work2018
  center_sq := center_sq2018
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2018.1
  jac_ok := checks2018.2.1
  accepted := checks2018.2.2

def tau2019 : RatBall :=
  ⟨⟨-73/320, 21/64⟩, 3/640⟩
def center2019 : GaussianRat :=
  ⟨-172956611/1000000000, 222066431/1000000000⟩
def contact2019 : RatBall := localContactBall tau2019 center2019
def work2019 : RoundedTauEval :=
  evalTau precision tau2019 contact2019 logTwoBall

theorem center_sq2019 : (center2019.re : ℝ)^2 +
    (center2019.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2019]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2019 : work2019.theta.ok = true ∧
    work2019.jac.invOK = true ∧ acceptsUnitSq work2019.out = true := by decide +kernel

def cell2019 : CellCertificate where
  tauBall := tau2019
  contactCenter := center2019
  contactBall := contact2019
  work := work2019
  center_sq := center_sq2019
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2019.1
  jac_ok := checks2019.2.1
  accepted := checks2019.2.2

def tau2020 : RatBall :=
  ⟨⟨-71/320, 21/64⟩, 3/640⟩
def center2020 : GaussianRat :=
  ⟨-168468823/1000000000, 55699379/250000000⟩
def contact2020 : RatBall := localContactBall tau2020 center2020
def work2020 : RoundedTauEval :=
  evalTau precision tau2020 contact2020 logTwoBall

theorem center_sq2020 : (center2020.re : ℝ)^2 +
    (center2020.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2020]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2020 : work2020.theta.ok = true ∧
    work2020.jac.invOK = true ∧ acceptsUnitSq work2020.out = true := by decide +kernel

def cell2020 : CellCertificate where
  tauBall := tau2020
  contactCenter := center2020
  contactBall := contact2020
  work := work2020
  center_sq := center_sq2020
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2020.1
  jac_ok := checks2020.2.1
  accepted := checks2020.2.2

def tau2021 : RatBall :=
  ⟨⟨-69/320, 21/64⟩, 3/640⟩
def center2021 : GaussianRat :=
  ⟨-81980819/500000000, 223513477/1000000000⟩
def contact2021 : RatBall := localContactBall tau2021 center2021
def work2021 : RoundedTauEval :=
  evalTau precision tau2021 contact2021 logTwoBall

theorem center_sq2021 : (center2021.re : ℝ)^2 +
    (center2021.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2021]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2021 : work2021.theta.ok = true ∧
    work2021.jac.invOK = true ∧ acceptsUnitSq work2021.out = true := by decide +kernel

def cell2021 : CellCertificate where
  tauBall := tau2021
  contactCenter := center2021
  contactBall := contact2021
  work := work2021
  center_sq := center_sq2021
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2021.1
  jac_ok := checks2021.2.1
  accepted := checks2021.2.2

def tau2022 : RatBall :=
  ⟨⟨-69/320, 107/320⟩, 3/640⟩
def center2022 : GaussianRat :=
  ⟨-20584937/125000000, 228038057/1000000000⟩
def contact2022 : RatBall := localContactBall tau2022 center2022
def work2022 : RoundedTauEval :=
  evalTau precision tau2022 contact2022 logTwoBall

theorem center_sq2022 : (center2022.re : ℝ)^2 +
    (center2022.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2022]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2022 : work2022.theta.ok = true ∧
    work2022.jac.invOK = true ∧ acceptsUnitSq work2022.out = true := by decide +kernel

def cell2022 : CellCertificate where
  tauBall := tau2022
  contactCenter := center2022
  contactBall := contact2022
  work := work2022
  center_sq := center_sq2022
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2022.1
  jac_ok := checks2022.2.1
  accepted := checks2022.2.2

def tau2023 : RatBall :=
  ⟨⟨-67/320, 21/64⟩, 3/640⟩
def center2023 : GaussianRat :=
  ⟨-79717703/500000000, 224213933/1000000000⟩
def contact2023 : RatBall := localContactBall tau2023 center2023
def work2023 : RoundedTauEval :=
  evalTau precision tau2023 contact2023 logTwoBall

theorem center_sq2023 : (center2023.re : ℝ)^2 +
    (center2023.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2023 : work2023.theta.ok = true ∧
    work2023.jac.invOK = true ∧ acceptsUnitSq work2023.out = true := by decide +kernel

def cell2023 : CellCertificate where
  tauBall := tau2023
  contactCenter := center2023
  contactBall := contact2023
  work := work2023
  center_sq := center_sq2023
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2023.1
  jac_ok := checks2023.2.1
  accepted := checks2023.2.2

def cells : List CellCertificate := [cell2016, cell2017, cell2018, cell2019, cell2020, cell2021, cell2022, cell2023]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252

end


