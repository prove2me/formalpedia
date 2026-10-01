-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T21:00:00.900544+00:00
-- url     : https://prove2.me/theorems/a0d7938f-8d94-4270-893c-6f6cb08d4db1
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0357EndpointWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0357EndpointWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses
open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar
open E8TAxisFirstCellInverseCoverage E8TAxisProd0357Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem wholeBUpper_yBox_eq : (yBox wholeBUpperInput).d0 = wholeBUpperYBox := by decide +kernel

theorem wholeBUpper_contains :
    wholeBUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.wholeBInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.wholeBInput.alpha = ((2040637016713598987314498814201704474493346497704 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeBUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.wholeBInput.alpha) := by
    rw [e]; exact point_contains precision 2040637016713598987314498814201704474493346497704
  have h := checked_yBox_d0_contains (i := wholeBUpperInput) (we := wholeBUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeBUpper_primitive_checks.1 wholeBUpper_primitive_checks.2 endpointLogTwo_checked
    wholeBUpper_denominators ha
  rw [wholeBUpper_yBox_eq] at h
  exact h

def wholeCLowerAlpha : DyadicInterval precision := ⟨800789093237051640993320341704292036401494020410, 800789093237051640993320341704292036401494020410⟩
def wholeCLowerExp : DyadicInterval precision := ⟨488517571229872190688465166626124636106968690514, 488517571229872190688465166626124636106968692563⟩
def wholeCLowerLog : DyadicInterval precision := ⟨421460238264099943405098418906670736005341510180, 421460238264099943405098418906670736005341511979⟩
def wholeCLowerYBox : DyadicInterval precision := ⟨4196336576186355003892330075936627620187096009888, 4196336576186355003892330075936627620187096040608⟩
def wholeCLowerInput : Inputs precision :=
  ⟨wholeCLowerAlpha, wholeCLowerExp, wholeCLowerLog, endpointLogTwo⟩
def wholeCLowerExpWitness : ExpWitness precision :=
  ⟨488517571229872190688465166626124636106968690514, scale precision, 488517571229872190688465166626124636106968692563, scale precision,
    1, 128, 1, 128,
    ⟨-1601578186474103281986640683408584072802988044338, -1601578186474103281986640683408584072802988043796⟩, ⟨-1601578186474103281986640683408584072802988038208, -1601578186474103281986640683408584072802988037666⟩⟩

theorem wholeCLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCLowerAlpha) wholeCLowerExp wholeCLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCLowerExp) wholeCLowerLog fastLogWitness = true := by decide +kernel

theorem wholeCLower_denominators : DenominatorsPositive wholeCLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCLower_yBox_eq : (yBox wholeCLowerInput).d0 = wholeCLowerYBox := by decide +kernel

theorem wholeCLower_contains :
    wholeCLowerYBox.Contains (Y (lower E8TAxisProd0357PaddedInputs.wholeCInput.alpha)) := by
  have e : lower E8TAxisProd0357PaddedInputs.wholeCInput.alpha = ((800789093237051640993320341704292036401494020410 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCLowerInput.alpha.Contains (lower E8TAxisProd0357PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 800789093237051640993320341704292036401494020410
  have h := checked_yBox_d0_contains (i := wholeCLowerInput) (we := wholeCLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCLower_primitive_checks.1 wholeCLower_primitive_checks.2 endpointLogTwo_checked
    wholeCLower_denominators ha
  rw [wholeCLower_yBox_eq] at h
  exact h

def wholeCUpperAlpha : DyadicInterval precision := ⟨813174903790675435270300547776661299147946481061, 813174903790675435270300547776661299147946481061⟩
def wholeCUpperExp : DyadicInterval precision := ⟨480307253047982564333142441600660835470557427697, 480307253047982564333142441600660835470557429746⟩
def wholeCUpperLog : DyadicInterval precision := ⟨415293773064665725797602136077825515073744450946, 415293773064665725797602136077825515073744452749⟩
def wholeCUpperYBox : DyadicInterval precision := ⟨4250686168324597956163029605653264394980551576202, 4250686168324597956163029605653264394980551607490⟩
def wholeCUpperInput : Inputs precision :=
  ⟨wholeCUpperAlpha, wholeCUpperExp, wholeCUpperLog, endpointLogTwo⟩
def wholeCUpperExpWitness : ExpWitness precision :=
  ⟨480307253047982564333142441600660835470557427697, scale precision, 480307253047982564333142441600660835470557429746, scale precision,
    1, 128, 1, 128,
    ⟨-1626349807581350870540601095553322598295892965692, -1626349807581350870540601095553322598295892965148⟩, ⟨-1626349807581350870540601095553322598295892959454, -1626349807581350870540601095553322598295892958914⟩⟩

theorem wholeCUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCUpperAlpha) wholeCUpperExp wholeCUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCUpperExp) wholeCUpperLog fastLogWitness = true := by decide +kernel

theorem wholeCUpper_denominators : DenominatorsPositive wholeCUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeCUpper_yBox_eq : (yBox wholeCUpperInput).d0 = wholeCUpperYBox := by decide +kernel

theorem wholeCUpper_contains :
    wholeCUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.wholeCInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.wholeCInput.alpha = ((813174903790675435270300547776661299147946481061 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeCUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.wholeCInput.alpha) := by
    rw [e]; exact point_contains precision 813174903790675435270300547776661299147946481061
  have h := checked_yBox_d0_contains (i := wholeCUpperInput) (we := wholeCUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeCUpper_primitive_checks.1 wholeCUpper_primitive_checks.2 endpointLogTwo_checked
    wholeCUpper_denominators ha
  rw [wholeCUpper_yBox_eq] at h
  exact h

def wholeDLowerAlpha : DyadicInterval precision := ⟨797886217135535601213561462349015058648188238211, 797886217135535601213561462349015058648188238211⟩
def wholeDLowerExp : DyadicInterval precision := ⟨490462045819898463991457369988920387637474808101, 490462045819898463991457369988920387637474810150⟩
def wholeDLowerLog : DyadicInterval precision := ⟨422916858198723400101802834922666847715950885810, 422916858198723400101802834922666847715950887607⟩
def wholeDLowerYBox : DyadicInterval precision := ⟨4183548436859709603358047833650360143765106599779, 4183548436859709603358047833650360143765106630359⟩
def wholeDLowerInput : Inputs precision :=
  ⟨wholeDLowerAlpha, wholeDLowerExp, wholeDLowerLog, endpointLogTwo⟩
def wholeDLowerExpWitness : ExpWitness precision :=
  ⟨490462045819898463991457369988920387637474808101, scale precision, 490462045819898463991457369988920387637474810150, scale precision,
    1, 128, 1, 128,
    ⟨-1595772434271071202427122924698030117296376479932, -1595772434271071202427122924698030117296376479388⟩, ⟨-1595772434271071202427122924698030117296376473826, -1595772434271071202427122924698030117296376473284⟩⟩

theorem wholeDLower_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDLowerAlpha) wholeDLowerExp wholeDLowerExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDLowerExp) wholeDLowerLog fastLogWitness = true := by decide +kernel

theorem wholeDLower_denominators : DenominatorsPositive wholeDLowerInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDLower_yBox_eq : (yBox wholeDLowerInput).d0 = wholeDLowerYBox := by decide +kernel

theorem wholeDLower_contains :
    wholeDLowerYBox.Contains (Y (lower E8TAxisProd0357PaddedInputs.wholeDInput.alpha)) := by
  have e : lower E8TAxisProd0357PaddedInputs.wholeDInput.alpha = ((797886217135535601213561462349015058648188238211 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDLowerInput.alpha.Contains (lower E8TAxisProd0357PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 797886217135535601213561462349015058648188238211
  have h := checked_yBox_d0_contains (i := wholeDLowerInput) (we := wholeDLowerExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDLower_primitive_checks.1 wholeDLower_primitive_checks.2 endpointLogTwo_checked
    wholeDLower_denominators ha
  rw [wholeDLower_yBox_eq] at h
  exact h

def wholeDUpperAlpha : DyadicInterval precision := ⟨809836502735595761416983074307699172577520947592, 809836502735595761416983074307699172577520947592⟩
def wholeDUpperExp : DyadicInterval precision := ⟨482506534178222248007502303634473307517593158085, 482506534178222248007502303634473307517593160134⟩
def wholeDUpperLog : DyadicInterval precision := ⟨416948124396604742320674577430730286078596387504, 416948124396604742320674577430730286078596389309⟩
def wholeDUpperYBox : DyadicInterval precision := ⟨4236071151951288926980992757326101564783992251334, 4236071151951288926980992757326101564783992282483⟩
def wholeDUpperInput : Inputs precision :=
  ⟨wholeDUpperAlpha, wholeDUpperExp, wholeDUpperLog, endpointLogTwo⟩
def wholeDUpperExpWitness : ExpWitness precision :=
  ⟨482506534178222248007502303634473307517593158085, scale precision, 482506534178222248007502303634473307517593160134, scale precision,
    1, 128, 1, 128,
    ⟨-1619673005471191522833966148615398345155041898738, -1619673005471191522833966148615398345155041898194⟩, ⟨-1619673005471191522833966148615398345155041892532, -1619673005471191522833966148615398345155041891990⟩⟩

theorem wholeDUpper_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDUpperAlpha) wholeDUpperExp wholeDUpperExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDUpperExp) wholeDUpperLog fastLogWitness = true := by decide +kernel

theorem wholeDUpper_denominators : DenominatorsPositive wholeDUpperInput := by
  unfold DenominatorsPositive
  decide +kernel

theorem wholeDUpper_yBox_eq : (yBox wholeDUpperInput).d0 = wholeDUpperYBox := by decide +kernel

theorem wholeDUpper_contains :
    wholeDUpperYBox.Contains (Y (upper E8TAxisProd0357PaddedInputs.wholeDInput.alpha)) := by
  have e : upper E8TAxisProd0357PaddedInputs.wholeDInput.alpha = ((809836502735595761416983074307699172577520947592 : ℤ) : ℝ) / (scale precision : ℝ) := rfl
  have ha : wholeDUpperInput.alpha.Contains (upper E8TAxisProd0357PaddedInputs.wholeDInput.alpha) := by
    rw [e]; exact point_contains precision 809836502735595761416983074307699172577520947592
  have h := checked_yBox_d0_contains (i := wholeDUpperInput) (we := wholeDUpperExpWitness)
    (wl := fastLogWitness) (wL := fastLogWitness)
    wholeDUpper_primitive_checks.1 wholeDUpper_primitive_checks.2 endpointLogTwo_checked
    wholeDUpper_denominators ha
  rw [wholeDUpper_yBox_eq] at h
  exact h

theorem centerA_covers_slope {s : ℝ} (hs : s ∈ Icc (centerT) (centerT)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerALower_contains centerAUpper_contains _ _ hs
  · norm_num [centerALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerA_covers :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerAInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerT) :=
  centerA_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * centerS + centerT) (2 * centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerBLower_contains centerBUpper_contains _ _ hs
  · norm_num [centerBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerB_covers :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerBInput.alpha.Contains a ∧
      0 < a ∧ Y a = (2 * centerS + centerT) :=
  centerB_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerC_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS + centerT) (centerS + centerT)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerCLower_contains centerCUpper_contains _ _ hs
  · norm_num [centerCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerC_covers :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerCInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS + centerT) :=
  centerC_covers_slope ⟨le_rfl, le_rfl⟩

theorem centerD_covers_slope {s : ℝ} (hs : s ∈ Icc (centerS) (centerS)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    centerDLower_contains centerDUpper_contains _ _ hs
  · norm_num [centerDLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [centerDUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem centerD_covers :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.centerDInput.alpha.Contains a ∧
      0 < a ∧ Y a = (centerS) :=
  centerD_covers_slope ⟨le_rfl, le_rfl⟩

theorem wholeA_covers_slope {s : ℝ} (hs : s ∈ Icc (tLower) (tUpper)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.wholeAInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeALower_contains wholeAUpper_contains _ _ hs
  · norm_num [wholeALowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeAUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeB_covers_slope {s : ℝ} (hs : s ∈ Icc (2 * sLower + tLower) (2 * sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.wholeBInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeBLower_contains wholeBUpper_contains _ _ hs
  · norm_num [wholeBLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeBUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

theorem wholeC_covers_slope {s : ℝ} (hs : s ∈ Icc (sLower + tLower) (sUpper + tUpper)) :
    ∃ a : ℝ, E8TAxisProd0357PaddedInputs.wholeCInput.alpha.Contains a ∧
      0 < a ∧ Y a = s := by
  apply covers_of_endpoint_enclosures (by decide) (by decide)
    wholeCLower_contains wholeCUpper_contains _ _ hs
  · norm_num [wholeCLowerYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]
  · norm_num [wholeCUpperYBox, scale, precision, centerS, centerT, sLower, sUpper, tLower, tUpper]

end GeneralCK.Certificates.E8TAxisProd0357EndpointWitnesses


