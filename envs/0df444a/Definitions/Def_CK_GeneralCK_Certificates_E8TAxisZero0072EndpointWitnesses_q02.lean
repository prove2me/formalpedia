-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T00:51:25.03668+00:00
-- url     : https://prove2.me/theorems/82c51f1a-e411-4c8c-a93a-3e3aded153d4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0072EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisZero0072Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisZero0072PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisZero0072PaddedInputs.wholeCInput.alpha = ((637832247480472324939326434952621888088044164628 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisZero0072PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 637832247480472324939326434952621888088044164628
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨649228718111606835228787531534818497469011380960, 649228718111606835228787531534818497469011380960⟩
def wholeCUpperExp : DyadicInterval precision := ⟨601110678192711313158291435371246245864325370595, 601110678192711313158291435371246245864325501668⟩
def wholeCUpperLog : DyadicInterval precision := ⟨503500274479321981929762507552810301429855848698, 503500274479321981929762507552810301429855942605⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨3502580017715842024907518431906617024294249906997, 3502580017715842024907518431906617024294251327810⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨601110678192711313158291435371246245864325370595, scale precision, 601110678192711313158291435371246245864325501668, scale precision,
    0, 512, 0, 512, ⟨-1298457436223213670457575063069636994938022922233, -1298457436223213670457575063069636994938022921190⟩, ⟨-1298457436223213670457575063069636994938022603553, -1298457436223213670457575063069636994938022602512⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisZero0072PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisZero0072PaddedInputs.wholeCInput.alpha = ((649228718111606835228787531534818497469011380960 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisZero0072PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 649228718111606835228787531534818497469011380960
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088044164628, 637832247480472324939326434952621888088044164628⟩
def wholeDLowerExp : DyadicInterval precision := ⟨610558820864912509175272747825498145069509045415, 610558820864912509175272747825498145069509176488⟩
def wholeDLowerLog : DyadicInterval precision := ⟨510179642243321146984571771117295506705446295854, 510179642243321146984571771117295506705446389343⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨3448230425577599072636818902189980249500634909578, 3448230425577599072636818902189980249500636301247⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498145069509045415, scale precision, 610558820864912509175272747825498145069509176488, scale precision,
    0, 512, 0, 512, ⟨-1275664494960944649878652869905243776176088487107, -1275664494960944649878652869905243776176088486068⟩, ⟨-1275664494960944649878652869905243776176088173359, -1275664494960944649878652869905243776176088172318⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisZero0072PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisZero0072PaddedInputs.wholeDInput.alpha = ((637832247480472324939326434952621888088044164628 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisZero0072PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 637832247480472324939326434952621888088044164628
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨648844592727412176647428020776866274458586684425, 648844592727412176647428020776866274458586684425⟩
def wholeDUpperExp : DyadicInterval precision := ⟨601426740197304508434017275821189106629622562571, 601426740197304508434017275821189106629622693644⟩
def wholeDUpperLog : DyadicInterval precision := ⟨503724208829984298099852655433700220931313262320, 503724208829984298099852655433700220931313356217⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨3500753140669178396259763825865721670519680007075, 3500753140669178396259763825865721670519681426913⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨601426740197304508434017275821189106629622562571, scale precision, 601426740197304508434017275821189106629622693644, scale precision,
    0, 512, 0, 512, ⟨-1297689185454824353294856041553732548917173529081, -1297689185454824353294856041553732548917173528040⟩, ⟨-1297689185454824353294856041553732548917173210563, -1297689185454824353294856041553732548917173209526⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisZero0072PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisZero0072PaddedInputs.wholeDInput.alpha = ((648844592727412176647428020776866274458586684425 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisZero0072PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 648844592727412176647428020776866274458586684425
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisZero0072PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisZero0072EndpointWitnesses


