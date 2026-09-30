-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0377
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0377
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:51:11.764623+00:00
-- url     : https://prove2.me/theorems/90eaaf30-fa26-4eaa-8590-70bdf0419eb6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0377.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau3016 : RatBall :=
  ⟨⟨51/640, -247/640⟩, 3/1280⟩
def center3016 : GaussianRat :=
  ⟨32518989/500000000, -70076353/250000000⟩
def contact3016 : RatBall := localContactBall tau3016 center3016
def work3016 : RoundedTauEval :=
  evalTau precision tau3016 contact3016 logTwoBall

theorem center_sq3016 : (center3016.re : ℝ)^2 +
    (center3016.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3016]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3016 : work3016.theta.ok = true ∧
    work3016.jac.invOK = true ∧ acceptsUnitSq work3016.out = true := by decide +kernel

def cell3016 : CellCertificate where
  tauBall := tau3016
  contactCenter := center3016
  contactBall := contact3016
  work := work3016
  center_sq := center_sq3016
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3016.1
  jac_ok := checks3016.2.1
  accepted := checks3016.2.2

def tau3017 : RatBall :=
  ⟨⟨49/640, -49/128⟩, 3/1280⟩
def center3017 : GaussianRat :=
  ⟨31164041/500000000, -277963583/1000000000⟩
def contact3017 : RatBall := localContactBall tau3017 center3017
def work3017 : RoundedTauEval :=
  evalTau precision tau3017 contact3017 logTwoBall

theorem center_sq3017 : (center3017.re : ℝ)^2 +
    (center3017.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3017]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3017 : work3017.theta.ok = true ∧
    work3017.jac.invOK = true ∧ acceptsUnitSq work3017.out = true := by decide +kernel

def cell3017 : CellCertificate where
  tauBall := tau3017
  contactCenter := center3017
  contactBall := contact3017
  work := work3017
  center_sq := center_sq3017
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3017.1
  jac_ok := checks3017.2.1
  accepted := checks3017.2.2

def tau3018 : RatBall :=
  ⟨⟨51/640, -49/128⟩, 3/1280⟩
def center3018 : GaussianRat :=
  ⟨3242521/50000000, -138890411/500000000⟩
def contact3018 : RatBall := localContactBall tau3018 center3018
def work3018 : RoundedTauEval :=
  evalTau precision tau3018 contact3018 logTwoBall

theorem center_sq3018 : (center3018.re : ℝ)^2 +
    (center3018.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3018]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3018 : work3018.theta.ok = true ∧
    work3018.jac.invOK = true ∧ acceptsUnitSq work3018.out = true := by decide +kernel

def cell3018 : CellCertificate where
  tauBall := tau3018
  contactCenter := center3018
  contactBall := contact3018
  work := work3018
  center_sq := center_sq3018
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3018.1
  jac_ok := checks3018.2.1
  accepted := checks3018.2.2

def tau3019 : RatBall :=
  ⟨⟨53/640, -247/640⟩, 3/1280⟩
def center3019 : GaussianRat :=
  ⟨33782393/500000000, -56022603/200000000⟩
def contact3019 : RatBall := localContactBall tau3019 center3019
def work3019 : RoundedTauEval :=
  evalTau precision tau3019 contact3019 logTwoBall

theorem center_sq3019 : (center3019.re : ℝ)^2 +
    (center3019.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3019]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3019 : work3019.theta.ok = true ∧
    work3019.jac.invOK = true ∧ acceptsUnitSq work3019.out = true := by decide +kernel

def cell3019 : CellCertificate where
  tauBall := tau3019
  contactCenter := center3019
  contactBall := contact3019
  work := work3019
  center_sq := center_sq3019
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3019.1
  jac_ok := checks3019.2.1
  accepted := checks3019.2.2

def tau3020 : RatBall :=
  ⟨⟨11/128, -247/640⟩, 3/1280⟩
def center3020 : GaussianRat :=
  ⟨70088901/1000000000, -139956777/500000000⟩
def contact3020 : RatBall := localContactBall tau3020 center3020
def work3020 : RoundedTauEval :=
  evalTau precision tau3020 contact3020 logTwoBall

theorem center_sq3020 : (center3020.re : ℝ)^2 +
    (center3020.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3020]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3020 : work3020.theta.ok = true ∧
    work3020.jac.invOK = true ∧ acceptsUnitSq work3020.out = true := by decide +kernel

def cell3020 : CellCertificate where
  tauBall := tau3020
  contactCenter := center3020
  contactBall := contact3020
  work := work3020
  center_sq := center_sq3020
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3020.1
  jac_ok := checks3020.2.1
  accepted := checks3020.2.2

def tau3021 : RatBall :=
  ⟨⟨53/640, -49/128⟩, 3/1280⟩
def center3021 : GaussianRat :=
  ⟨4210637/62500000, -55518211/200000000⟩
def contact3021 : RatBall := localContactBall tau3021 center3021
def work3021 : RoundedTauEval :=
  evalTau precision tau3021 contact3021 logTwoBall

theorem center_sq3021 : (center3021.re : ℝ)^2 +
    (center3021.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3021]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3021 : work3021.theta.ok = true ∧
    work3021.jac.invOK = true ∧ acceptsUnitSq work3021.out = true := by decide +kernel

def cell3021 : CellCertificate where
  tauBall := tau3021
  contactCenter := center3021
  contactBall := contact3021
  work := work3021
  center_sq := center_sq3021
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3021.1
  jac_ok := checks3021.2.1
  accepted := checks3021.2.2

def tau3022 : RatBall :=
  ⟨⟨11/128, -49/128⟩, 3/1280⟩
def center3022 : GaussianRat :=
  ⟨69887307/1000000000, -277394317/1000000000⟩
def contact3022 : RatBall := localContactBall tau3022 center3022
def work3022 : RoundedTauEval :=
  evalTau precision tau3022 contact3022 logTwoBall

theorem center_sq3022 : (center3022.re : ℝ)^2 +
    (center3022.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3022]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3022 : work3022.theta.ok = true ∧
    work3022.jac.invOK = true ∧ acceptsUnitSq work3022.out = true := by decide +kernel

def cell3022 : CellCertificate where
  tauBall := tau3022
  contactCenter := center3022
  contactBall := contact3022
  work := work3022
  center_sq := center_sq3022
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3022.1
  jac_ok := checks3022.2.1
  accepted := checks3022.2.2

def tau3023 : RatBall :=
  ⟨⟨49/640, -243/640⟩, 3/1280⟩
def center3023 : GaussianRat :=
  ⟨12430013/200000000, -275443499/1000000000⟩
def contact3023 : RatBall := localContactBall tau3023 center3023
def work3023 : RoundedTauEval :=
  evalTau precision tau3023 contact3023 logTwoBall

theorem center_sq3023 : (center3023.re : ℝ)^2 +
    (center3023.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center3023]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks3023 : work3023.theta.ok = true ∧
    work3023.jac.invOK = true ∧ acceptsUnitSq work3023.out = true := by decide +kernel

def cell3023 : CellCertificate where
  tauBall := tau3023
  contactCenter := center3023
  contactBall := contact3023
  work := work3023
  center_sq := center_sq3023
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks3023.1
  jac_ok := checks3023.2.1
  accepted := checks3023.2.2

def cells : List CellCertificate := [cell3016, cell3017, cell3018, cell3019, cell3020, cell3021, cell3022, cell3023]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377

end


