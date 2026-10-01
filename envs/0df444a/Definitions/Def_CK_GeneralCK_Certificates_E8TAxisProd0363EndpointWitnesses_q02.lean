-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T20:59:21.033463+00:00
-- url     : https://prove2.me/theorems/e87fb313-85f9-466d-a6c9-459434976501
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0363EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0363EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0363Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.wholeBInput.alpha = ((2110507658231659998199062601393666866215129023297 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2110507658231659998199062601393666866215129023297
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨823539509859430523244296081108954404821923024361, 823539509859430523244296081108954404821923024361⟩
def wholeCLowerExp : DyadicInterval precision := ⟨473542898439744410988485104098145145338656585546, 473542898439744410988485104098145145338656587595⟩
def wholeCLowerLog : DyadicInterval precision := ⟨410193696130617163810602601810729208044884095094, 410193696130617163810602601810729208044884096909⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4295901375229522765194956105165424400901156417188, 4295901375229522765194956105165424400901156448999⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨473542898439744410988485104098145145338656585546, scale precision, 473542898439744410988485104098145145338656587595, scale precision,
    1, 128, 1, 128,
    ⟨-1647079019718861046488592162217908809643846052330, -1647079019718861046488592162217908809643846051794⟩, ⟨-1647079019718861046488592162217908809643846046006, -1647079019718861046488592162217908809643846045468⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisProd0363PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisProd0363PaddedInputs.wholeCInput.alpha = ((823539509859430523244296081108954404821923024361 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisProd0363PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 823539509859430523244296081108954404821923024361
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨836071441462393785116710345027261493919777042186, 836071441462393785116710345027261493919777042186⟩
def wholeCUpperExp : DyadicInterval precision := ⟨465491164562179826958837533347876238027931101412, 465491164562179826958837533347876238027931103461⟩
def wholeCUpperLog : DyadicInterval precision := ⟨404099690161144398945313792480534184982830598434, 404099690161144398945313792480534184982830600259⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4350250967367765717465655634882061175694611976773, 4350250967367765717465655634882061175694612009205⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨465491164562179826958837533347876238027931101412, scale precision, 465491164562179826958837533347876238027931103461, scale precision,
    1, 128, 1, 128,
    ⟨-1672142882924787570233420690054522987839554088034, -1672142882924787570233420690054522987839554087498⟩, ⟨-1672142882924787570233420690054522987839554081602, -1672142882924787570233420690054522987839554081066⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.wholeCInput.alpha = ((836071441462393785116710345027261493919777042186 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 836071441462393785116710345027261493919777042186
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨821860677686075647293949968540300351172223413535, 821860677686075647293949968540300351172223413535⟩
def wholeDLowerExp : DyadicInterval precision := ⟨474632069948069015840646238761706423500880008558, 474632069948069015840646238761706423500880010607⟩
def wholeDLowerLog : DyadicInterval precision := ⟨411016094834480306545789264008568524744914547710, 411016094834480306545789264008568524744914549521⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨4288593867042868250603937681001842985802876754277, 4288593867042868250603937681001842985802876785991⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨474632069948069015840646238761706423500880008558, scale precision, 474632069948069015840646238761706423500880010607, scale precision,
    1, 128, 1, 128,
    ⟨-1643721355372151294587899937080600702344446830672, -1643721355372151294587899937080600702344446830134⟩, ⟨-1643721355372151294587899937080600702344446824362, -1643721355372151294587899937080600702344446823828⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisProd0363PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisProd0363PaddedInputs.wholeDInput.alpha = ((821860677686075647293949968540300351172223413535 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisProd0363PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 821860677686075647293949968540300351172223413535
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨833959591445470778384083818034390997094871400435, 833959591445470778384083818034390997094871400435⟩
def wholeDUpperExp : DyadicInterval precision := ⟨466838367135635595432846250236128803062991310477, 466838367135635595432846250236128803062991312526⟩
def wholeDUpperLog : DyadicInterval precision := ⟨405121100734994108525530084726425876454680179780, 405121100734994108525530084726425876454680181599⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4341116582134447574226882604677584406821762398752, 4341116582134447574226882604677584406821762431057⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨466838367135635595432846250236128803062991310477, scale precision, 466838367135635595432846250236128803062991312526, scale precision,
    1, 128, 1, 128,
    ⟨-1667919182890941556768167636068781994189742804524, -1667919182890941556768167636068781994189742803984⟩, ⟨-1667919182890941556768167636068781994189742798108, -1667919182890941556768167636068781994189742797570⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisProd0363PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisProd0363PaddedInputs.wholeDInput.alpha = ((833959591445470778384083818034390997094871400435 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisProd0363PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 833959591445470778384083818034390997094871400435
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerA_covers_slope {s : ℝ} (hs : s ∈ Icc (centerT) (centerT)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerALower_contains centerAUpper_contains _ _ hs
  · norm_num [centerALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerA_covers :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerT) :=
  centerA_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeA_covers_slope {s : ℝ} (hs : s ∈ Icc (tLower) (tUpper)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.wholeAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeALower_contains wholeAUpper_contains _ _ hs
  · norm_num [wholeALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0363PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisProd0363EndpointWitnesses


