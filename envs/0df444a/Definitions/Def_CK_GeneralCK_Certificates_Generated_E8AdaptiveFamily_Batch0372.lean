-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0372
-- name    : CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_Batch0372
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:05:45.734763+00:00
-- url     : https://prove2.me/theorems/4b2f2790-d8fa-4667-b0e7-698466e0e657
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8AdaptiveFamily/Batch0372.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticCellCertificateSchema

-- ===== source module GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372 =====
section

/-! Deterministically generated E8 adaptive derivative certificates. -/

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372

open E8GaussianRatBall E8RoundedRatBall E8ComplexLogBoxChecker
open E8CoupledTauCBox E8LocalContactBall E8RoundedDerivativeEvaluator
open E8QuadraticBallAcceptance E8QuadraticCellCertificateSchema

def tau2976 : RatBall :=
  ⟨⟨43/640, -251/640⟩, 3/1280⟩
def center2976 : GaussianRat :=
  ⟨2761527/50000000, -286093747/1000000000⟩
def contact2976 : RatBall := localContactBall tau2976 center2976
def work2976 : RoundedTauEval :=
  evalTau precision tau2976 contact2976 logTwoBall

theorem center_sq2976 : (center2976.re : ℝ)^2 +
    (center2976.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2976]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2976 : work2976.theta.ok = true ∧
    work2976.jac.invOK = true ∧ acceptsUnitSq work2976.out = true := by decide +kernel

def cell2976 : CellCertificate where
  tauBall := tau2976
  contactCenter := center2976
  contactBall := contact2976
  work := work2976
  center_sq := center_sq2976
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2976.1
  jac_ok := checks2976.2.1
  accepted := checks2976.2.2

def tau2977 : RatBall :=
  ⟨⟨41/640, -249/640⟩, 3/1280⟩
def center2977 : GaussianRat :=
  ⟨13130217/250000000, -283703773/1000000000⟩
def contact2977 : RatBall := localContactBall tau2977 center2977
def work2977 : RoundedTauEval :=
  evalTau precision tau2977 contact2977 logTwoBall

theorem center_sq2977 : (center2977.re : ℝ)^2 +
    (center2977.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2977]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2977 : work2977.theta.ok = true ∧
    work2977.jac.invOK = true ∧ acceptsUnitSq work2977.out = true := by decide +kernel

def cell2977 : CellCertificate where
  tauBall := tau2977
  contactCenter := center2977
  contactBall := contact2977
  work := work2977
  center_sq := center_sq2977
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2977.1
  jac_ok := checks2977.2.1
  accepted := checks2977.2.2

def tau2978 : RatBall :=
  ⟨⟨43/640, -249/640⟩, 3/1280⟩
def center2978 : GaussianRat :=
  ⟨13766751/250000000, -141772517/500000000⟩
def contact2978 : RatBall := localContactBall tau2978 center2978
def work2978 : RoundedTauEval :=
  evalTau precision tau2978 contact2978 logTwoBall

theorem center_sq2978 : (center2978.re : ℝ)^2 +
    (center2978.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2978]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2978 : work2978.theta.ok = true ∧
    work2978.jac.invOK = true ∧ acceptsUnitSq work2978.out = true := by decide +kernel

def cell2978 : CellCertificate where
  tauBall := tau2978
  contactCenter := center2978
  contactBall := contact2978
  work := work2978
  center_sq := center_sq2978
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2978.1
  jac_ok := checks2978.2.1
  accepted := checks2978.2.2

def tau2979 : RatBall :=
  ⟨⟨9/128, -251/640⟩, 3/1280⟩
def center2979 : GaussianRat :=
  ⟨57781797/1000000000, -285925371/1000000000⟩
def contact2979 : RatBall := localContactBall tau2979 center2979
def work2979 : RoundedTauEval :=
  evalTau precision tau2979 contact2979 logTwoBall

theorem center_sq2979 : (center2979.re : ℝ)^2 +
    (center2979.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2979]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2979 : work2979.theta.ok = true ∧
    work2979.jac.invOK = true ∧ acceptsUnitSq work2979.out = true := by decide +kernel

def cell2979 : CellCertificate where
  tauBall := tau2979
  contactCenter := center2979
  contactBall := contact2979
  work := work2979
  center_sq := center_sq2979
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2979.1
  jac_ok := checks2979.2.1
  accepted := checks2979.2.2

def tau2980 : RatBall :=
  ⟨⟨47/640, -251/640⟩, 3/1280⟩
def center2980 : GaussianRat :=
  ⟨1508267/25000000, -71437399/250000000⟩
def contact2980 : RatBall := localContactBall tau2980 center2980
def work2980 : RoundedTauEval :=
  evalTau precision tau2980 contact2980 logTwoBall

theorem center_sq2980 : (center2980.re : ℝ)^2 +
    (center2980.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2980]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2980 : work2980.theta.ok = true ∧
    work2980.jac.invOK = true ∧ acceptsUnitSq work2980.out = true := by decide +kernel

def cell2980 : CellCertificate where
  tauBall := tau2980
  contactCenter := center2980
  contactBall := contact2980
  work := work2980
  center_sq := center_sq2980
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2980.1
  jac_ok := checks2980.2.1
  accepted := checks2980.2.2

def tau2981 : RatBall :=
  ⟨⟨9/128, -249/640⟩, 3/1280⟩
def center2981 : GaussianRat :=
  ⟨28805449/500000000, -141689483/500000000⟩
def contact2981 : RatBall := localContactBall tau2981 center2981
def work2981 : RoundedTauEval :=
  evalTau precision tau2981 contact2981 logTwoBall

theorem center_sq2981 : (center2981.re : ℝ)^2 +
    (center2981.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2981]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2981 : work2981.theta.ok = true ∧
    work2981.jac.invOK = true ∧ acceptsUnitSq work2981.out = true := by decide +kernel

def cell2981 : CellCertificate where
  tauBall := tau2981
  contactCenter := center2981
  contactBall := contact2981
  work := work2981
  center_sq := center_sq2981
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2981.1
  jac_ok := checks2981.2.1
  accepted := checks2981.2.2

def tau2982 : RatBall :=
  ⟨⟨47/640, -249/640⟩, 3/1280⟩
def center2982 : GaussianRat :=
  ⟨60152449/1000000000, -283205599/1000000000⟩
def contact2982 : RatBall := localContactBall tau2982 center2982
def work2982 : RoundedTauEval :=
  evalTau precision tau2982 contact2982 logTwoBall

theorem center_sq2982 : (center2982.re : ℝ)^2 +
    (center2982.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2982]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2982 : work2982.theta.ok = true ∧
    work2982.jac.invOK = true ∧ acceptsUnitSq work2982.out = true := by decide +kernel

def cell2982 : CellCertificate where
  tauBall := tau2982
  contactCenter := center2982
  contactBall := contact2982
  work := work2982
  center_sq := center_sq2982
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2982.1
  jac_ok := checks2982.2.1
  accepted := checks2982.2.2

def tau2983 : RatBall :=
  ⟨⟨33/640, -247/640⟩, 3/1280⟩
def center2983 : GaussianRat :=
  ⟨8438273/200000000, -281713577/1000000000⟩
def contact2983 : RatBall := localContactBall tau2983 center2983
def work2983 : RoundedTauEval :=
  evalTau precision tau2983 contact2983 logTwoBall

theorem center_sq2983 : (center2983.re : ℝ)^2 +
    (center2983.im : ℝ)^2 ≤ (1/9 : ℝ) := by
  norm_num [center2983]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checks2983 : work2983.theta.ok = true ∧
    work2983.jac.invOK = true ∧ acceptsUnitSq work2983.out = true := by decide +kernel

def cell2983 : CellCertificate where
  tauBall := tau2983
  contactCenter := center2983
  contactBall := contact2983
  work := work2983
  center_sq := center_sq2983
  contact_eq := rfl
  work_eq := rfl
  theta_ok := checks2983.1
  jac_ok := checks2983.2.1
  accepted := checks2983.2.2

def cells : List CellCertificate := [cell2976, cell2977, cell2978, cell2979, cell2980, cell2981, cell2982, cell2983]

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372

end


